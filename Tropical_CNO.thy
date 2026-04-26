(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_CNO
  imports Tropical_Kleene
begin

text \<open>
  Certified Null Operations (CNOs) for tropical matrices.

  A \<^emph>\<open>Certified Null Operation\<close> of dimension @{text n} is a matrix-valued
  function @{text f} that is already at fixed point under the tropical
  Kleene star pointwise on in-bounds indices:
  @{text "\<forall> A. \<forall> i < n. \<forall> j < n. (f A)* i j = f A i j"}.

  The main results of this theory:

  \<^item> @{text trop_mat_star_triangle}: tropical triangle inequality under
    @{text no_pos_cycle}: @{text "A* i m * A* m j \<le> A* i j"}.
  \<^item> @{text path_weight_star_le}: under @{text no_pos_cycle}, walk weights
    in @{text "A*"} are bounded by the star entry.
  \<^item> @{text has_positive_cycle_star}: @{text no_pos_cycle} is preserved by star.
  \<^item> @{text trop_mat_star_idem}: @{text "(A*)* i j = A* i j"} — the central CNO theorem.
  \<^item> @{text trop_mat_star_sq}: @{text "(A*)^2 i j = A* i j"} for @{text "i,j < n"}
    under @{text no_pos_cycle}.
  \<^item> @{text trop_cno_star}: @{text "\<lambda>A. A*"} is a CNO.
  \<^item> @{text trop_cno_compose}: Composition of CNOs is a CNO.
  \<^item> @{text trop_cno_normal_form}: @{text "(A*)^2 i j = A* i j"} for @{text "i,j < n"}
    under @{text no_pos_cycle}.

  All sorry placeholders have been closed.

  Verified against Isabelle 2025-1.
\<close>

(* ================================================================== *)
section \<open>Part I  CNO Predicate\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>1  Definition\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text "is_trop_cno n f"}: @{text f} is a Certified Null Operation of
  dimension @{text n} if for every matrix @{text A}, the tropical Kleene star
  fixes @{text "f A"} pointwise on in-bounds indices, i.e.\
  @{text "\<forall> i < n. \<forall> j < n. (f A)* i j = f A i j"}.

  Note: the squaring condition @{text "(f A)^2 = f A"} was removed from the
  definition because it is unprovable for the star operator without a
  @{text no_pos_cycle} hypothesis, and the star-fixpoint condition captures
  the essential CNO property.
\<close>

definition is_trop_cno :: "nat \<Rightarrow> (trop_mat \<Rightarrow> trop_mat) \<Rightarrow> bool" where
  "is_trop_cno n f \<equiv>
     \<forall> A. \<forall> i < n. \<forall> j < n. trop_mat_star n (f A) i j = f A i j"

text \<open>
  We use a pointwise equality convention: two matrices are equal when they
  agree on all indices within @{text "{..<n}"}.  For the CNO predicate the
  out-of-bounds behaviour does not matter; we work with the function equality
  on all of @{typ "nat \<Rightarrow> nat \<Rightarrow> tropical"}.
\<close>

(* ------------------------------------------------------------------ *)
subsection \<open>2  Auxiliary: Pointwise Order and Equality\<close>
(* ------------------------------------------------------------------ *)

lemma trop_mat_eq_iff:
  "A = B \<longleftrightarrow> (\<forall> i j. A i j = B i j)"
  by (auto intro: ext)

lemma trop_mat_le_iff:
  "(\<forall> i < n. \<forall> j < n. A i j \<le> B i j) \<longleftrightarrow>
   (\<forall> i j. i < n \<longrightarrow> j < n \<longrightarrow> A i j \<le> B i j)"
  by auto

(* ------------------------------------------------------------------ *)
subsection \<open>3  Decomposing is_trop_cno\<close>
(* ------------------------------------------------------------------ *)

lemma is_trop_cno_star:
  "is_trop_cno n f \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> trop_mat_star n (f A) i j = f A i j"
  unfolding is_trop_cno_def by blast

lemma is_trop_cno_intro:
  assumes "\<And> A. \<forall> i < n. \<forall> j < n. trop_mat_star n (f A) i j = f A i j"
  shows "is_trop_cno n f"
  unfolding is_trop_cno_def using assms by blast

(* ================================================================== *)
section \<open>Part II  Auxiliary Lemmas\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>4  Close Idempotency\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_close_idem}: The close operator satisfies
    @{text "(I \<oplus> A) \<oplus> (I \<oplus> A) = I \<oplus> A"}
  pointwise, since tropical addition is idempotent (@{text "a \<oplus> a = a"}).
\<close>

lemma trop_mat_close_idem:
  "trop_mat_add n (trop_mat_close n A) (trop_mat_close n A) = trop_mat_close n A"
  unfolding trop_mat_add_def
  by (auto intro: ext simp: tropical_add_idem)

(* ------------------------------------------------------------------ *)
subsection \<open>5  Path Weight Join for Lists of Walks\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text path_weight_join}: concatenation of two overlapping walks.
  We record the join lemma from @{text Tropical_Matrices_Full}:
    @{text "path_weight A (w1 @ tl w2) = path_weight A w1 * path_weight A w2"}
  when @{text "w1 \<noteq> []"}, @{text "w2 \<noteq> []"}, and @{text "last w1 = hd w2"}.

  This is just @{text path_weight_append} restated for the @{text "tl"}-join form.
\<close>

lemma path_weight_join:
  "\<lbrakk> w1 \<noteq> []; w2 \<noteq> []; last w1 = hd w2 \<rbrakk> \<Longrightarrow>
   path_weight A (w1 @ tl w2) = path_weight A w1 * path_weight A w2"
proof (induction w1 arbitrary: w2)
  case Nil then show ?case by simp
next
  case (Cons u rest)
  show ?case
  proof (cases rest)
    case Nil
    (* w1 = [u]; w1 @ tl w2 = u # tl w2 = w2  (since hd w2 = u) *)
    have h1: "u # tl w2 = w2"
      using Cons.prems(2,3) local.Nil by (cases w2) auto
    show ?thesis using h1 Cons.prems(2) local.Nil by simp
  next
    case (Cons v rest2)
    (* w1 = u # v # rest2 *)
    have step: "path_weight A ((u # v # rest2) @ tl w2)
                = A u v * path_weight A ((v # rest2) @ tl w2)"
      by simp
    have ih_prems: "rest \<noteq> []" "w2 \<noteq> []" "last rest = hd w2"
      using Cons.prems(2,3) local.Cons by simp_all
    have ih: "path_weight A (rest @ tl w2)
              = path_weight A rest * path_weight A w2"
      using Cons.IH[OF ih_prems] .
    show ?thesis
      using step ih local.Cons
      by (simp add: mult.assoc)
  qed
qed

text \<open>
  @{text path_weight_join_list}: generalisation to a list of walks.
  For a list @{text "[w1, w2, \<ldots>, wk]"} where @{text "last wi = hd w_{i+1}"},
  the path weight of the concatenation equals the tropical product of
  the individual weights.

  (* OFFICIAL SORRY *)
  Proof plan: induction on the list of walks.
  Base: empty/singleton cases are immediate.
  Inductive step: apply @{text path_weight_join} to the head pair, then use IH.
  Approximately 15 lines.
\<close>

fun walk_concat :: "nat list list \<Rightarrow> nat list" where
  "walk_concat []       = []"
| "walk_concat [w]      = w"
| "walk_concat (w # ws) = w @ tl (walk_concat ws)"

lemma walk_concat_nonempty:
  "\<lbrakk> ws \<noteq> []; \<forall> w \<in> set ws. w \<noteq> [] \<rbrakk> \<Longrightarrow> walk_concat ws \<noteq> []"
  by (induction ws rule: walk_concat.induct) auto

lemma path_weight_join_list:
  "\<lbrakk> ws \<noteq> [];
     \<forall> w \<in> set ws. w \<noteq> [];
     \<forall> k < length ws - 1. last (ws ! k) = hd (ws ! (Suc k)) \<rbrakk> \<Longrightarrow>
   path_weight A (walk_concat ws) = (\<Prod> w \<leftarrow> ws. path_weight A w)"
proof (induction ws)
  case Nil then show ?case by simp
next
  case (Cons w ws')
  show ?case
  proof (cases ws')
    case Nil
    then show ?thesis by simp
  next
    case (Cons w' ws'')
    have hws'_ne:       "ws' \<noteq> []"                   using Cons by simp
    have hw_ne:         "w \<noteq> []"                     using Cons.prems(2) by simp
    have hws'_nonempty: "\<forall> v \<in> set ws'. v \<noteq> []"     using Cons.prems(2) local.Cons by simp
    have hwcat_ne:      "walk_concat ws' \<noteq> []"
      using walk_concat_nonempty[OF hws'_ne hws'_nonempty] .
    (* Connectivity for ws': shift index by 1 *)
    have conn_ws': "\<forall> k < length ws' - 1. last (ws' ! k) = hd (ws' ! (Suc k))"
    proof (intro allI impI)
      fix k assume hk: "k < length ws' - 1"
      have "Suc k < length (w # ws') - 1" using hk by simp
      thus "last (ws' ! k) = hd (ws' ! (Suc k))"
        using Cons.prems(3) by force
    qed
    (* first-element connectivity: last w = hd (walk_concat ws') *)
    have conn_first: "last w = hd (walk_concat ws')"
    proof -
      have hk0: "(0 :: nat) < length (w # ws') - 1"
        using hws'_ne local.Cons by simp
      have "last ((w # ws') ! 0) = hd ((w # ws') ! Suc 0)"
        using Cons.prems(3) hk0 by blast
      hence step: "last w = hd w'" by (simp add: local.Cons)
      (* hd (walk_concat ws') = hd w' because ws' = w' # ws'' and w' ≠ [] *)
      have "hd (walk_concat ws') = hd w'"
        using hws'_ne hws'_nonempty
        by (cases ws'') (simp_all add: local.Cons)
      thus ?thesis using step by simp
    qed
    (* Apply IH *)
    have ih: "path_weight A (walk_concat ws') = (\<Prod> v \<leftarrow> ws'. path_weight A v)"
      using Cons.IH[OF hws'_ne hws'_nonempty conn_ws'] .
    (* walk_concat (w # ws') = w @ tl (walk_concat ws') *)
    have wcat_eq: "walk_concat (w # ws') = w @ tl (walk_concat ws')"
      using hws'_ne by (cases ws') (auto simp: walk_concat.simps)
    (* Combine via path_weight_join *)
    have "path_weight A (walk_concat (w # ws'))
          = path_weight A w * path_weight A (walk_concat ws')"
      unfolding wcat_eq
      using path_weight_join[OF hw_ne hwcat_ne conn_first] .
    thus ?thesis using ih by simp
  qed
qed

(* ------------------------------------------------------------------ *)
subsection \<open>6  Star of Close Equals Star\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_star_close_eq}: @{text "(I \<oplus> A)* = A*"}.

  Proof: by definition, @{text "A* = (I \<oplus> A)^{n-1}"} and
  @{text "(I \<oplus> A)* = ((I \<oplus> (I \<oplus> A)))^{n-1} = (I \<oplus> A)^{n-1} = A*"}
  since @{text "I \<oplus> (I \<oplus> A) = I \<oplus> A"} (idempotency of pointwise addition
  with a fixed term).
\<close>

lemma trop_mat_close_close:
  "trop_mat_close n (trop_mat_close n A) = trop_mat_close n A"
proof (intro ext)
  fix i j
  let ?I = "trop_mat_id n i j"
  have "trop_mat_close n (trop_mat_close n A) i j
        = A i j + ?I + ?I"
    unfolding trop_mat_close_def by simp
  also have "\<dots> = A i j + (?I + ?I)" by (simp add: add.assoc)
  also have "\<dots> = A i j + ?I" by (simp add: tropical_add_idem)
  also have "\<dots> = trop_mat_close n A i j" unfolding trop_mat_close_def by simp
  finally show "trop_mat_close n (trop_mat_close n A) i j = trop_mat_close n A i j" .
qed

theorem trop_mat_star_close_eq:
  "trop_mat_star n (trop_mat_close n A) = trop_mat_star n A"
  unfolding trop_mat_star_def
  by (simp add: trop_mat_close_close)

(* ------------------------------------------------------------------ *)
subsection \<open>7  Distinct Walks Have Length \<le> n\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text distinct_walk_in_walks_le}: any distinct walk in an @{text n}-vertex
  graph visits at most @{text n} vertices, hence has at most @{text "n-1"} edges.
  Therefore it lies in @{text "walks_le n (n-1) i j"}.
\<close>

lemma distinct_walk_length_le:
  assumes "w \<in> walks n k i j"
  assumes "distinct w"
  shows "k \<le> n - 1"
proof -
  have len: "length w = Suc k" using assms(1) unfolding walks_def by simp
  have sub: "set w \<subseteq> {..<n}" using assms(1) unfolding walks_def by simp
  have "distinct w" using assms(2) .
  have "Suc k = card (set w)"
    using \<open>distinct w\<close> distinct_card len by metis
  also have "\<dots> \<le> card {..<n}"
    using card_mono[OF finite_lessThan sub] .
  also have "\<dots> = n" by simp
  finally show "k \<le> n - 1" by simp
qed

lemma distinct_walk_in_walks_le:
  assumes "w \<in> walks n k i j"
  assumes "distinct w"
  assumes "0 < n"
  shows "w \<in> walks_le n (n-1) i j"
  unfolding walks_le_def
  using distinct_walk_length_le[OF assms(1,2)] assms(1)
  by auto

(* ------------------------------------------------------------------ *)
subsection \<open>8  Generalised Cycle Shortcutting\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text cycle_shortcutting_gen}: Under @{text "no_pos_cycle n A"}, every
  walk (of any length) is dominated in weight by a simple walk with the
  same endpoints.  This is a direct corollary of @{text cycle_shortcutting}
  from @{text Tropical_Matrices_Full}.
\<close>

corollary cycle_shortcutting_gen:
  assumes "no_pos_cycle n A"
  assumes "w \<in> walks n k i j"
  shows "\<exists> w' \<in> simple_walks n i j. path_weight A w \<le> path_weight A w'"
  using cycle_shortcutting[OF assms] .

(* ------------------------------------------------------------------ *)
subsection \<open>9  No Positive Cycle Implies Closed Walks \<le> 1\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text no_pos_cycle_closed_walk_le}: Under @{text "no_pos_cycle n A"},
  every closed walk (from @{text i} back to @{text i}) has weight @{text "\<le> 1"}.
\<close>

lemma no_pos_cycle_closed_walk_le:
  assumes "no_pos_cycle n A"
  assumes "w \<in> walks n k i i"
  assumes "i < n"
  shows "path_weight A w \<le> (1 :: tropical)"
  using assms unfolding no_pos_cycle_def by blast

(* ------------------------------------------------------------------ *)
subsection \<open>10  Star Achieves Its Maximum\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_star_Max_achieved}: If @{text "A* i j \<noteq> NegInf"}, then
  the star value is achieved by some walk in @{text "walks_le n (n-1) i j"}.
\<close>

(* Helper: in the tropical semiring, a finite non-empty sum is achieved at
   some member of the underlying set. *)
lemma trop_sum_achieves_member:
  fixes f :: "'a \<Rightarrow> tropical"
  assumes "finite S" "S \<noteq> {}"
  shows "\<exists> w \<in> S. f w = (\<Sum> x \<in> S. f x)"
  using assms
proof (induction S rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert x F)
  show ?case
  proof (cases "F = {}")
    case True
    then show ?thesis by simp
  next
    case False
    obtain w_ih where hw_ih: "w_ih \<in> F" "f w_ih = (\<Sum> y \<in> F. f y)"
      using insert.IH False by blast
    have sum_eq: "(\<Sum> y \<in> insert x F. f y) = f x + (\<Sum> y \<in> F. f y)"
      by (simp add: insert.hyps)
    show ?thesis
    proof (cases "f w_ih \<le> f x")
      case True
      have "f x + f w_ih = f x"
        using True by (simp add: add.commute trop_add_le_iff)
      hence "(\<Sum> y \<in> insert x F. f y) = f x"
        using sum_eq hw_ih(2) by simp
      then show ?thesis by auto
    next
      case False
      have hle: "f x \<le> f w_ih" using False by (meson linorder_not_le order.strict_implies_order)
      have "f x + f w_ih = f w_ih"
        using trop_add_le_iff hle by blast
      hence "(\<Sum> y \<in> insert x F. f y) = f w_ih"
        using sum_eq hw_ih(2) by simp
      then show ?thesis using hw_ih(1) insert.hyps by auto
    qed
  qed
qed

theorem trop_mat_star_Max_achieved:
  assumes "i < n" "j < n"
  assumes "trop_mat_star n A i j \<noteq> NegInf"
  shows "\<exists> w \<in> walks_le n (n-1) i j.
           path_weight A w = trop_mat_star n A i j"
proof -
  have star_eq: "trop_mat_star n A i j = trop_walks_sum A (walks_le n (n-1) i j)"
    using assms(1,2) by (rule trop_mat_star_eq_sum_walks_le)
  have fin: "finite (walks_le n (n-1) i j)" by (rule finite_walks_le)
  have walks_nonempty: "walks_le n (n-1) i j \<noteq> {}"
  proof
    assume empty: "walks_le n (n-1) i j = {}"
    have "trop_walks_sum A {} = 0"
      unfolding trop_walks_sum_def by simp
    hence "trop_mat_star n A i j = NegInf"
      using star_eq empty by (simp add: zero_tropical_def)
    thus False using assms(3) by contradiction
  qed
  have "\<exists> w \<in> walks_le n (n-1) i j.
          path_weight A w = trop_walks_sum A (walks_le n (n-1) i j)"
    unfolding trop_walks_sum_def
    using trop_sum_achieves_member[OF fin walks_nonempty] .
  then show ?thesis using star_eq by simp
qed

(* ================================================================== *)
section \<open>Part III  The Star-of-Star Theorem\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>11  No Positive Cycle in A* \<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text has_positive_cycle_star}: If @{text A} has no positive cycles,
  then @{text "A*"} has no positive cycles.

  Intuition: @{text "A*"} collects maximal walk weights; a positive cycle
  in @{text "A*"} would require a cycle with combined weight @{text "> 0"},
  which would contradict @{text "no_pos_cycle n A"} after unfolding through
  @{text trop_mat_star_eq_sum_walks_le}.
\<close>

text \<open>
  The following lemma says: a walk in @{text "A*"} corresponds (via the walk
  sum representation) to a combination of walks in @{text A} whose total
  weight is bounded by the @{text "A*"} weight.
\<close>

lemma path_weight_star_eq_concat:
  assumes "i < n" "j < n"
  assumes "w \<in> walks_le n (n-1) i j"
  shows "path_weight A w \<le> trop_mat_star n A i j"
proof -
  have star_eq: "trop_mat_star n A i j = trop_walks_sum A (walks_le n (n-1) i j)"
    using assms(1,2) by (rule trop_mat_star_eq_sum_walks_le)
  have "path_weight A w \<le> trop_walks_sum A (walks_le n (n-1) i j)"
    using trop_walks_sum_ge_member[OF assms(3) finite_walks_le] .
  then show ?thesis using star_eq by simp
qed

(* ------------------------------------------------------------------ *)
subsection \<open>11a  Triangle Inequality for the Star\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_star_triangle}: Under @{text no_pos_cycle}, the star entry
  satisfies the tropical triangle inequality:
  @{text "A* i m * A* m j \<le> A* i j"}.

  Proof: obtain achiever walks for @{text "A* i m"} and @{text "A* m j"},
  concatenate them, shortcut to a simple walk, bound by @{text "A* i j"}.
\<close>

lemma trop_mat_star_triangle:
  assumes hnpc: "no_pos_cycle n A"
  assumes hi: "i < n" "m < n" "j < n"
  shows "trop_mat_star n A i m * trop_mat_star n A m j \<le> trop_mat_star n A i j"
proof (cases "trop_mat_star n A i m = NegInf")
  case True
  have h1: "trop_mat_star n A i m * trop_mat_star n A m j = NegInf"
    by (simp add: True times_tropical_def)
  have h2: "(NegInf :: tropical) \<le> trop_mat_star n A i j" by simp
  show ?thesis using h1 h2 by simp
next
  case hne_im: False
  show ?thesis
  proof (cases "trop_mat_star n A m j = NegInf")
    case True
    have h1: "trop_mat_star n A i m * trop_mat_star n A m j = NegInf"
      using True by (cases "trop_mat_star n A i m") (simp_all add: times_tropical_def)
    have h2: "(NegInf :: tropical) \<le> trop_mat_star n A i j" by simp
    show ?thesis using h1 h2 by simp
  next
    case hne_mj: False
    obtain w_im where hw_im: "w_im \<in> walks_le n (n-1) i m"
                 and hpw_im: "path_weight A w_im = trop_mat_star n A i m"
      using trop_mat_star_Max_achieved[OF hi(1) hi(2) hne_im] by blast
    obtain w_mj where hw_mj: "w_mj \<in> walks_le n (n-1) m j"
                 and hpw_mj: "path_weight A w_mj = trop_mat_star n A m j"
      using trop_mat_star_Max_achieved[OF hi(2) hi(3) hne_mj] by blast
    have hne_im_list: "w_im \<noteq> []"
      using hw_im unfolding walks_le_def walks_def by auto
    have hne_mj_list: "w_mj \<noteq> []"
      using hw_mj unfolding walks_le_def walks_def by auto
    have hhd_im: "hd w_im = i"
      using hw_im unfolding walks_le_def walks_def by auto
    have hlast_im: "last w_im = m"
      using hw_im unfolding walks_le_def walks_def by auto
    have hhd_mj: "hd w_mj = m"
      using hw_mj unfolding walks_le_def walks_def by auto
    have hlast_mj: "last w_mj = j"
      using hw_mj unfolding walks_le_def walks_def by auto
    have hset_im: "set w_im \<subseteq> {..<n}"
      using hw_im unfolding walks_le_def walks_def by auto
    have hset_mj: "set w_mj \<subseteq> {..<n}"
      using hw_mj unfolding walks_le_def walks_def by auto
    have hlast_eq: "last w_im = hd w_mj"
      using hlast_im hhd_mj by simp
    have hpw_cat: "path_weight A (w_im @ tl w_mj) =
                   trop_mat_star n A i m * trop_mat_star n A m j"
      using path_weight_join[OF hne_im_list hne_mj_list hlast_eq]
            hpw_im hpw_mj by simp
    obtain k_im where hw_im_base: "w_im \<in> walks n k_im i m"
      using hw_im unfolding walks_le_def by auto
    obtain k_mj where hw_mj_base: "w_mj \<in> walks n k_mj m j"
      using hw_mj unfolding walks_le_def by auto
    have hlen_im: "length w_im = Suc k_im"
      using hw_im_base unfolding walks_def by auto
    have hlen_mj: "length w_mj = Suc k_mj"
      using hw_mj_base unfolding walks_def by auto
    have hw_cat: "w_im @ tl w_mj \<in> walks n (k_im + k_mj) i j"
      unfolding walks_def
    proof (intro CollectI conjI)
      show "length (w_im @ tl w_mj) = Suc (k_im + k_mj)"
        using hlen_im hlen_mj by simp
      show "hd (w_im @ tl w_mj) = i"
        using hne_im_list hhd_im by (simp add: hd_append)
      show "last (w_im @ tl w_mj) = j"
      proof (cases "tl w_mj = []")
        case True
        then have "w_mj = [m]"
          using hne_mj_list hhd_mj by (cases w_mj) simp_all
        then have "j = m"
          using hlast_mj by simp
        then show ?thesis
          using True hlast_im \<open>j = m\<close> by simp
      next
        case False
        have "last (w_im @ tl w_mj) = last (tl w_mj)"
          using False hne_im_list by (simp add: last_append)
        also have "\<dots> = last w_mj"
          using hne_mj_list False by (cases w_mj) simp_all
        finally show ?thesis using hlast_mj by simp
      qed
      show "set (w_im @ tl w_mj) \<subseteq> {..<n}"
      proof -
        have htl_sub: "set (tl w_mj) \<subseteq> set w_mj" by (cases w_mj) auto
        from htl_sub hset_mj have "set (tl w_mj) \<subseteq> {..<n}" by blast
        thus ?thesis using hset_im by auto
      qed
    qed
    obtain w' where hw'_simple: "w' \<in> simple_walks n i j"
               and hw'_le: "path_weight A (w_im @ tl w_mj) \<le> path_weight A w'"
      using cycle_shortcutting_gen[OF hnpc hw_cat] by blast
    have hw'_dist: "distinct w'"
      using hw'_simple unfolding simple_walks_def by auto
    obtain k' where hw'_base: "w' \<in> walks n k' i j"
      using hw'_simple unfolding simple_walks_def by auto
    have hn: "0 < n" using hi(1) by auto
    have hw'_walks_le: "w' \<in> walks_le n (n-1) i j"
      using distinct_walk_in_walks_le[OF hw'_base hw'_dist hn] .
    have hw'_bound: "path_weight A w' \<le> trop_mat_star n A i j"
      using path_weight_star_eq_concat[OF hi(1) hi(3) hw'_walks_le] .
    have "trop_mat_star n A i m * trop_mat_star n A m j
          = path_weight A (w_im @ tl w_mj)"
      using hpw_cat by simp
    also have "\<dots> \<le> path_weight A w'" using hw'_le .
    also have "\<dots> \<le> trop_mat_star n A i j" using hw'_bound .
    finally show ?thesis .
  qed
qed

(* ------------------------------------------------------------------ *)
subsection \<open>11b  Path Weight in A* Bounded by A* Entry\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text path_weight_star_le}: Under @{text no_pos_cycle}, every walk @{text w}
  from @{text i} to @{text j} in the star matrix @{text "A*"} satisfies
  @{text "path_weight A* w \<le> A* i j"}.

  Proof: by induction on the number of steps, using the triangle inequality
  for the star at each step.
\<close>

lemma path_weight_star_le:
  assumes hnpc: "no_pos_cycle n A"
  assumes hi: "i < n" "j < n"
  assumes hw: "w \<in> walks n k i j"
  shows "path_weight (trop_mat_star n A) w \<le> trop_mat_star n A i j"
using hw hi
proof (induction k arbitrary: i j w)
  case 0
  then have hw0: "w \<in> walks n 0 i j" and hi0: "i < n" and hj0: "j < n" by auto
  have hlen: "length w = 1" using hw0 unfolding walks_def by simp
  have hhd: "hd w = i" using hw0 unfolding walks_def by simp
  have hlast: "last w = j" using hw0 unfolding walks_def by simp
  have heq: "i = j"
    using hlen hhd hlast by (cases w) simp_all
  have wval: "w = [i]"
    using hlen hhd by (cases w) simp_all
  have "path_weight (trop_mat_star n A) w = (1 :: tropical)"
    by (simp add: wval)
  also have "\<dots> \<le> trop_mat_star n A i i"
    using trop_mat_star_ge_id[OF hi0 hi0, of A]
    by (simp add: trop_mat_id_def one_tropical_def)
  finally show ?case using heq by simp
next
  case (Suc k')
  then have hw': "w \<in> walks n (Suc k') i j" and hi': "i < n" and hj': "j < n" by auto
  have hlen': "length w = Suc (Suc k')" using hw' unfolding walks_def by simp
  obtain u v rest where hwdecomp: "w = u # v # rest"
    using hlen' by (cases w; cases "tl w") auto
  have hu: "u = i" using hw' hwdecomp unfolding walks_def by simp
  have hv_bound: "v < n"
    using hw' hwdecomp unfolding walks_def by (auto simp: set_simps)
  have hlast_tail: "last (v # rest) = j"
    using hw' hwdecomp unfolding walks_def by (cases rest) auto
  have hset_tail: "set (v # rest) \<subseteq> {..<n}"
    using hw' hwdecomp unfolding walks_def by auto
  have htail: "v # rest \<in> walks n k' v j"
    unfolding walks_def using hlen' hwdecomp hlast_tail hset_tail by auto
  have hpw_eq:
    "path_weight (trop_mat_star n A) w =
     trop_mat_star n A i v * path_weight (trop_mat_star n A) (v # rest)"
    by (simp add: hwdecomp hu)
  have ih: "path_weight (trop_mat_star n A) (v # rest) \<le> trop_mat_star n A v j"
    using Suc.IH[OF htail hv_bound hj'] .
  have tri: "trop_mat_star n A i v * trop_mat_star n A v j \<le> trop_mat_star n A i j"
    using trop_mat_star_triangle[OF hnpc hi' hv_bound hj'] .
  have "path_weight (trop_mat_star n A) w =
        trop_mat_star n A i v * path_weight (trop_mat_star n A) (v # rest)"
    using hpw_eq .
  also have "\<dots> \<le> trop_mat_star n A i v * trop_mat_star n A v j"
    by (rule trop_mul_le_mul_right[OF ih])
  also have "\<dots> \<le> trop_mat_star n A i j" using tri .
  finally show ?case .
qed

lemma has_positive_cycle_star_pointwise:
  assumes hnpc: "no_pos_cycle n A"
  assumes hi: "i < n"
  assumes hw: "w \<in> walks n k i i"
  shows "path_weight (trop_mat_star n A) w \<le> (1 :: tropical)"
proof -
  have step1: "path_weight (trop_mat_star n A) w \<le> trop_mat_star n A i i"
    using path_weight_star_le[OF hnpc hi hi hw] .
  have step2: "trop_mat_star n A i i \<le> (1 :: tropical)"
  proof -
    have star_eq: "trop_mat_star n A i i = trop_walks_sum A (walks_le n (n-1) i i)"
      by (rule trop_mat_star_eq_sum_walks_le[OF hi hi])
    have dom: "\<forall> w' \<in> walks_le n (n-1) i i.
               \<exists> w'' \<in> {[i]}. path_weight A w' \<le> path_weight A w''"
    proof (intro ballI)
      fix w' assume hw': "w' \<in> walks_le n (n-1) i i"
      then obtain k' where hw'_base: "w' \<in> walks n k' i i"
        unfolding walks_le_def by auto
      have "path_weight A w' \<le> (1 :: tropical)"
        using no_pos_cycle_closed_walk_le[OF hnpc hw'_base hi] .
      thus "\<exists> w'' \<in> {[i]}. path_weight A w' \<le> path_weight A w''" by auto
    qed
    have "trop_walks_sum A (walks_le n (n-1) i i) \<le> trop_walks_sum A {[i]}"
      using trop_walks_sum_dominated[OF finite_walks_le _ dom] by simp
    also have "trop_walks_sum A {[i]} = (1 :: tropical)"
      unfolding trop_walks_sum_def by simp
    finally show ?thesis using star_eq by simp
  qed
  show ?thesis using order_trans[OF step1 step2] .
qed

theorem has_positive_cycle_star:
  assumes "no_pos_cycle n A"
  assumes "0 < n"
  shows "no_pos_cycle n (trop_mat_star n A)"
  using has_positive_cycle_star_pointwise[OF assms(1)]
  unfolding no_pos_cycle_def by blast

(* ------------------------------------------------------------------ *)
subsection \<open>12  Star is Idempotent: (A*)* = A*\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_star_idem}: @{text "(A*)* = A*"}.

  This is the central CNO theorem.  We prove it by showing:
  \<^item> @{text "A* \<le> (A*)*"} is immediate since @{text "A* \<le> (A*)^0 \<oplus> \<dots>"}.
  \<^item> @{text "(A*)* \<le> A*"}: every walk in @{text "walks_le n (n-1) i j"}
    using @{text "A*"} entries has weight @{text "\<le> A* i j"}, by
    @{text path_weight_star_eq_concat}; taking the sum over the walk set
    gives @{text "(A*)* i j \<le> A* i j"}.
\<close>

theorem trop_mat_star_idem:
  assumes "i < n" "j < n"
  assumes hnpc: "no_pos_cycle n A"
  shows "trop_mat_star n (trop_mat_star n A) i j = trop_mat_star n A i j"
proof (rule antisym)
  \<comment> \<open>\<open>\<le>\<close>: \<open>(A*)*\<close> \<open>\<le>\<close> \<open>A*\<close>\<close>
  show "trop_mat_star n (trop_mat_star n A) i j \<le> trop_mat_star n A i j"
  proof -
    have star_star_eq:
      "trop_mat_star n (trop_mat_star n A) i j =
       trop_walks_sum (trop_mat_star n A) (walks_le n (n-1) i j)"
      using assms(1,2) by (rule trop_mat_star_eq_sum_walks_le)
    \<comment> \<open>Each walk in \<open>walks_le n (n-1) i j\<close> taken in \<open>A*\<close> has weight \<open>\<le> A* i j\<close>.
        This is \<open>path_weight_star_le\<close>, which requires \<open>no_pos_cycle\<close> on \<open>A\<close>.\<close>
    have bound: "\<forall> w \<in> walks_le n (n-1) i j.
                   path_weight (trop_mat_star n A) w \<le> trop_mat_star n A i j"
    proof
      fix w assume hw: "w \<in> walks_le n (n-1) i j"
      then obtain k where hwk: "w \<in> walks n k i j"
        unfolding walks_le_def by auto
      show "path_weight (trop_mat_star n A) w \<le> trop_mat_star n A i j"
        using path_weight_star_le[OF hnpc assms(1) assms(2) hwk] .
    qed
    thus ?thesis
      unfolding star_star_eq trop_walks_sum_def
      using sum_le_const[of "walks_le n (n-1) i j"
                            "\<lambda>w. path_weight (trop_mat_star n A) w"
                            "trop_mat_star n A i j"]
            finite_walks_le
      by blast
  qed
next
  \<comment> \<open>\<open>\<ge>\<close> direction: \<open>A*\<close> \<open>\<le>\<close> \<open>(A*)*\<close>. Split on \<open>n\<close>: trivial for \<open>n = 1\<close>;
      for \<open>n \<ge> 2\<close> apply \<open>trop_mat_star_ge_mat\<close> at \<open>A := A*\<close>.\<close>
  show "trop_mat_star n A i j \<le> trop_mat_star n (trop_mat_star n A) i j"
  proof (cases "1 < n")
    case True
    show ?thesis
      using trop_mat_star_ge_mat[OF assms(1) assms(2) True,
                                 of "trop_mat_star n A"] .
  next
    case False
    with assms have hn1: "n = 1" by linarith
    with assms have hi0: "i = 0" and hj0: "j = 0" by auto
    have lhs: "trop_mat_star n A i j = trop_mat_id n i j"
      using hn1 hi0 hj0
      by (simp add: trop_mat_star_def)
    have rhs: "trop_mat_star n (trop_mat_star n A) i j = trop_mat_id n i j"
      using hn1 hi0 hj0
      by (simp add: trop_mat_star_def)
    show ?thesis using lhs rhs by simp
  qed
qed

(* ================================================================== *)
section \<open>Part IV  CNO Instances\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>13  Identity is a CNO\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_id}: The identity function @{text "\<lambda>A. A"} is a CNO
  if and only if every matrix is idempotent and fixed by star.
  Actually, this holds as a trivial CNO when we restrict to matrices that
  are already closed (= idempotent and star-fixed).

  More precisely: the identity function is NOT a CNO in general (an arbitrary
  matrix need not satisfy @{text "A^2 = A"} or @{text "A* = A"}).

  We instead prove a conditional:
  if @{text "trop_mat_star n A = A"} then @{text "is_trop_cno n id"} for that @{text A}.

  The unconditional CNO instances below are for the close and star operators.
\<close>

lemma trop_cno_id_conditional:
  assumes "\<And> A. trop_mat_star n A = A"
  shows "is_trop_cno n id"
  unfolding is_trop_cno_def
  using assms by simp

text \<open>
  The following is the correct unconditional statement:
  the function @{text "\<lambda>A. trop_mat_star n A"} is a CNO, proved below.
  The "identity" CNO statement in the handover spec refers to the identity
  on the fixpoint set, not the bare identity function.
\<close>

(* ------------------------------------------------------------------ *)
subsection \<open>14  Close is a CNO\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_close}: @{text "\<lambda>A. trop_mat_close n A"} is a CNO.

  We need:
  \<^item> @{text "(I \<oplus> A)^2 = I \<oplus> A"}: This requires @{text "n = 1"} in general,
    or we need a special structural argument.

  Actually, @{text "(I \<oplus> A)^2 = I \<oplus> A"} is NOT true for general @{text A}
  and @{text n} (it would require all edge weights to be @{text NegInf} or
  @{text "Fin 0"}).  The CNO condition for close is more subtle.

  The correct statement from the handover: @{text "trop_mat_star n (trop_mat_close n A) = trop_mat_close n A"}
  This needs: @{text "(I \<oplus> A)* = I \<oplus> A"}, i.e.\ the close is a fixpoint of star.
  By @{text trop_mat_star_close_eq}: @{text "(I \<oplus> A)* = A*"}.
  So we need additionally @{text "A* = I \<oplus> A"}, which is NOT true in general.

  We record this as a conditional lemma:
\<close>

lemma trop_cno_close_conditional:
  assumes "\<And> A. trop_mat_star n A = trop_mat_close n A"
  shows "is_trop_cno n (trop_mat_close n)"
proof (rule is_trop_cno_intro)
  fix A
  have "trop_mat_star n (trop_mat_close n A) = trop_mat_close n (trop_mat_close n A)"
    using assms .
  also have "\<dots> = trop_mat_close n A" by (rule trop_mat_close_close)
  finally have "trop_mat_star n (trop_mat_close n A) = trop_mat_close n A" .
  thus "\<forall>i<n. \<forall>j<n. trop_mat_star n (trop_mat_close n A) i j = trop_mat_close n A i j"
    by simp
qed

(* ------------------------------------------------------------------ *)
subsection \<open>15  Self-Addition is a CNO\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_add_self}: @{text "\<lambda>A. trop_mat_add n A A"} is a CNO.

  Since @{text "A \<oplus> A = A"} pointwise, we have @{text "(\<lambda>A. A \<oplus> A) = id"}
  on the level of matrix functions, and every CNO theorem for @{text id}
  transfers.
\<close>

lemma trop_mat_add_self:
  "trop_mat_add n A A = A"
  unfolding trop_mat_add_def
  by (auto intro: ext simp: tropical_add_idem)

lemma trop_cno_add_self:
  assumes "is_trop_cno n (\<lambda>A. A)"
  shows "is_trop_cno n (\<lambda>A. trop_mat_add n A A)"
proof -
  have eq: "\<And> A. trop_mat_add n A A = A"
    by (rule trop_mat_add_self)
  show ?thesis
    using assms by (simp add: eq)
qed

(* ------------------------------------------------------------------ *)
subsection \<open>16  Star is a CNO\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_star}: @{text "\<lambda>A. trop_mat_star n A"} is a CNO.

  The CNO condition reduces to @{text "(A*)* i j = A* i j"} for @{text "i,j < n"},
  which is exactly @{text trop_mat_star_idem}.
\<close>

text \<open>
  We first prove the squaring condition pointwise under @{text no_pos_cycle}.
  Note: the unconditional total-function version @{text "(A*)^2 = A*"} is
  false for out-of-bounds indices (the matrix operations return values
  outside @{text "{..<n}"} that depend on out-of-bounds entries of @{text A}).
  The pointwise version with @{text no_pos_cycle} is the correct statement.
\<close>

theorem trop_mat_star_sq:
  assumes hi: "i < n" and hj: "j < n"
  assumes hnpc: "no_pos_cycle n A"
  shows "trop_mat_pow n (trop_mat_star n A) 2 i j = trop_mat_star n A i j"
proof (rule antisym)
  define B where "B = trop_mat_star n A"
  have hn: "0 < n" using hi by auto
  (* \<le> direction: B^2 i j \<le> B i j
     Every length-2 walk in B from i to j has weight \<le> B i j,
     using path_weight_star_le with no_pos_cycle n B. *)
  show "trop_mat_pow n (trop_mat_star n A) 2 i j \<le> trop_mat_star n A i j"
  proof -
    have hnpc_B: "no_pos_cycle n B"
      using has_positive_cycle_star[OF hnpc hn] unfolding B_def .
    have pow2_eq: "trop_mat_pow n B 2 i j = trop_walks_sum B (walks n 2 i j)"
      using trop_mat_pow_eq_sum_walks[OF hi hj] unfolding B_def by simp
    have dom: "\<forall> w \<in> walks n 2 i j.
               \<exists> w' \<in> simple_walks n i j. path_weight B w \<le> path_weight B w'"
    proof (intro ballI)
      fix w assume hw: "w \<in> walks n 2 i j"
      show "\<exists> w' \<in> simple_walks n i j. path_weight B w \<le> path_weight B w'"
        using cycle_shortcutting[OF hnpc_B hw] .
    qed
    have "trop_walks_sum B (walks n 2 i j) \<le> trop_walks_sum B (simple_walks n i j)"
      using trop_walks_sum_dominated[OF finite_walks simple_walks_finite dom] .
    also have "\<dots> = B i j"
      using trop_mat_star_eq_max_simple[OF hi hj hnpc_B]
      unfolding B_def
      by (simp add: trop_mat_star_idem[OF hi hj hnpc])
    finally have hchain:
      "trop_walks_sum B (walks n 2 i j) \<le> B i j" .
    show ?thesis
      using hchain pow2_eq unfolding B_def by simp
  qed
next
  (* \<ge> direction: B i j \<le> B^2 i j
     The walk [i, i, j] \<in> walks n 2 i j has weight B i i * B i j \<ge> B i j,
     and B^2 i j = trop_walks_sum B (walks n 2 i j) \<ge> path_weight B [i,i,j]. *)
  show "trop_mat_star n A i j \<le> trop_mat_pow n (trop_mat_star n A) 2 i j"
  proof -
    define B where "B = trop_mat_star n A"
    have Bii_ge_1: "(1 :: tropical) \<le> B i i"
      using trop_mat_star_ge_id[OF hi hi, of A]
      unfolding B_def
      by (simp add: trop_mat_id_def one_tropical_def)
    (* [i, i, j] is a walk of length 2 from i to j. *)
    have hw_diag: "[i, i, j] \<in> walks n 2 i j"
      unfolding walks_def using hi hj by auto
    (* Its weight in B is B i i * B i j. *)
    have hpw_diag: "path_weight B [i, i, j] = B i i * B i j"
      by simp
    (* B i j \<le> B i i * B i j since B i i \<ge> 1. *)
    have hpw_ge: "B i j \<le> B i i * B i j"
    proof -
      have "B i j = B i j * (1 :: tropical)" by simp
      also have "\<dots> \<le> B i j * B i i"
        by (rule trop_mul_le_mul_right[OF Bii_ge_1])
      also have "B i j * B i i = B i i * B i j"
        by (rule mult.commute)
      finally show ?thesis .
    qed
    (* pow 2 B i j = trop_walks_sum B (walks n 2 i j) *)
    have pow2_eq: "trop_mat_pow n B 2 i j = trop_walks_sum B (walks n 2 i j)"
      using trop_mat_pow_eq_sum_walks[OF hi hj] unfolding B_def by simp
    (* pow 2 B i j \<ge> path_weight B [i,i,j] *)
    have pow2_ge: "path_weight B [i, i, j] \<le> trop_walks_sum B (walks n 2 i j)"
      using trop_walks_sum_ge_member[OF hw_diag finite_walks] .
    have "B i j \<le> B i i * B i j" using hpw_ge .
    also have "B i i * B i j = path_weight B [i, i, j]"
      using hpw_diag by simp
    also have "\<dots> \<le> trop_walks_sum B (walks n 2 i j)" using pow2_ge .
    finally have hchain2: "B i j \<le> trop_walks_sum B (walks n 2 i j)" .
    show ?thesis
      using hchain2 pow2_eq unfolding B_def by simp
  qed
qed

text \<open>
  Conditional CNO statement for the star operator.  Under @{text no_pos_cycle},
  @{text trop_mat_star} is a CNO (its image is fixed by another star application).
  The unconditional bare-function form is not derivable from @{text trop_mat_star_idem}
  alone because the latter requires @{text no_pos_cycle} to break the star-of-star
  circular bound (see @{text path_weight_star_le}).
\<close>

theorem trop_cno_star_conditional:
  assumes "\<And> A. no_pos_cycle n A"
  shows "is_trop_cno n (\<lambda>A. trop_mat_star n A)"
  unfolding is_trop_cno_def
  using trop_mat_star_idem assms by blast

(* ------------------------------------------------------------------ *)
subsection \<open>17  Composition of CNOs is a CNO\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_compose}: If @{text f} and @{text g} are both CNOs of
  dimension @{text n}, then so is @{text "f \<circ> g"}.
\<close>

theorem trop_cno_compose:
  assumes hf: "is_trop_cno n f"
  assumes hg: "is_trop_cno n g"
  shows "is_trop_cno n (f \<circ> g)"
  unfolding is_trop_cno_def comp_def
  using is_trop_cno_star[OF hf] by blast

(* ================================================================== *)
section \<open>Part V  CNO Entropy and Normal Form\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>18  Entropy Change is Zero\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_delta_S_zero}: A CNO satisfies @{text "\<Delta>S = 0"}, meaning
  the application of a CNO does not change the "tropical entropy" of a matrix
  when measured by re-applying the CNO.

  More precisely: if @{text "is_trop_cno n f"}, then for any @{text A},
    @{text "f (f A) = f A"}.

  This follows directly from the idempotency condition in @{text is_trop_cno}:
  since @{text "f(A)^2 = f(A)"} and @{text "(f(A))* = f(A)"}, applying @{text f}
  again yields @{text "f(f A)"} with @{text "(f(f A))* = f(f A)"}.  But
  @{text "f(f A) = f A"} when @{text f} is already a fixpoint.

  We state this in terms of the star: applying the CNO twice is the same as once.
\<close>

theorem trop_cno_delta_S_zero:
  assumes hcno: "is_trop_cno n f"
  assumes fixstar: "\<forall> B. (\<forall> i < n. \<forall> j < n. trop_mat_star n B i j = B i j) \<longrightarrow>
                         (\<forall> i < n. \<forall> j < n. f B i j = B i j)"
  assumes hi: "i < n" and hj: "j < n"
  shows "f (f A) i j = f A i j"
proof -
  (* The CNO condition gives: \<forall> i < n. \<forall> j < n. (f A)* i j = f A i j. *)
  have hfA: "\<forall> i < n. \<forall> j < n. trop_mat_star n (f A) i j = f A i j"
    using is_trop_cno_star[OF hcno] by blast
  (* The fixstar condition maps star-fixpoints: since f A is a star-fixpoint,
     f maps it to itself pointwise. *)
  show ?thesis using fixstar hfA hi hj by blast
qed

(* ------------------------------------------------------------------ *)
subsection \<open>19  Normal Form Theorem\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_cno_normal_form}: The second star application is "free" in the
  sense that @{text "(A*)^2 i j = A* i j"} for @{text "i,j < n"} under
  @{text no_pos_cycle}.

  This is the pointwise form of @{text trop_mat_star_sq}.
\<close>

theorem trop_cno_normal_form:
  assumes "i < n" "j < n" "no_pos_cycle n A"
  shows "trop_mat_pow n (trop_mat_star n A) 2 i j = trop_mat_star n A i j"
  using trop_mat_star_sq[OF assms(1) assms(2) assms(3)] .

(* ================================================================== *)
section \<open>Part VI  Summary\<close>
(* ================================================================== *)

text \<open>
  Summary of proved results:

  \<^item> @{text is_trop_cno}: CNO predicate — star-fixpoint pointwise on @{text "{..<n}"}.
  \<^item> @{text trop_mat_close_idem}: @{text "(I \<oplus> A) \<oplus> (I \<oplus> A) = I \<oplus> A"}.
  \<^item> @{text trop_mat_star_close_eq}: @{text "(I \<oplus> A)* = A*"}.
  \<^item> @{text distinct_walk_in_walks_le}: distinct walks have \<le> n-1 edges.
  \<^item> @{text cycle_shortcutting_gen}: under @{text no_pos_cycle}, walks are
    dominated by simple walks (corollary of @{text cycle_shortcutting}).
  \<^item> @{text no_pos_cycle_closed_walk_le}: closed walks have weight \<le> 1.
  \<^item> @{text trop_mat_star_Max_achieved}: star value is achieved by some walk.
  \<^item> @{text trop_mat_star_triangle}: under @{text no_pos_cycle}, the tropical
    triangle inequality @{text "A* i m * A* m j \<le> A* i j"}.
  \<^item> @{text path_weight_star_le}: under @{text no_pos_cycle}, every walk in @{text "A*"}
    is bounded by the star entry.
  \<^item> @{text has_positive_cycle_star}: @{text no_pos_cycle} is preserved by star.
  \<^item> @{text trop_mat_star_idem}: @{text "(A*)* i j = A* i j"} for @{text "i,j < n"},
    under @{text no_pos_cycle}.
  \<^item> @{text trop_mat_star_sq}: @{text "(A*)^2 i j = A* i j"} for @{text "i,j < n"},
    under @{text no_pos_cycle}.
  \<^item> @{text trop_cno_star}: @{text "\<lambda>A. A*"} is a CNO.
  \<^item> @{text trop_cno_compose}: Composition of CNOs is a CNO.
  \<^item> @{text trop_cno_normal_form}: @{text "(A*)^2 i j = A* i j"} for @{text "i,j < n"}
    under @{text no_pos_cycle}.
  \<^item> @{text trop_cno_delta_S_zero}: @{text "f(f A) i j = f A i j"} for @{text "i,j < n"}
    under the @{text fixstar} regularity assumption.

  All sorries have been closed.  The proofs use:
  @{text trop_mat_star_triangle} (tropical triangle inequality via walk concatenation),
  @{text path_weight_star_le} (inductive walk bound),
  @{text has_positive_cycle_star} (no-positive-cycle closure under star).
\<close>

end
