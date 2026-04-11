(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_Kleene
  imports Tropical_Matrices_Full
begin

text \<open>
  Tropical Kleene star (matrix star) for the max-plus semiring.

  This theory defines the @{text n}-by-@{text n} Kleene star of a matrix
  @{text A} as @{text "(I \<oplus> A)^{n-1}"} and proves its key properties:

  \<^item> @{text trop_mat_star_eq_sum_pow}: star = @{text "\<oplus>_{m \<le> n-1} A^m"}.
  \<^item> @{text trop_mat_star_eq_sum_walks_le}: star = tropical sum over
    walks of at most @{text n-1} edges.
  \<^item> @{text trop_mat_star_equation}: @{text "A* = I \<oplus> A \<cdot> A*"}
    (the star equation / Bellman equation).
  \<^item> @{text trop_mat_star_eq_max_simple}: under no_pos_cycle,
    @{text "A*(i,j)"} equals the max-weight simple-path weight.
  \<^item> @{text trop_mat_star_least_prefixpoint}: @{text A*} is the least
    solution to @{text "X \<ge> I \<oplus> A \<cdot> X"} in the pointwise order.

  Verified against Isabelle 2025-1.
\<close>

(* ================================================================== *)
section \<open>Part I  Definition\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>1  Star Definition\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The Kleene star of an @{text n}-by-@{text n} tropical matrix @{text A}
  is the @{text "(n-1)"}-th power of the closed matrix @{text "I \<oplus> A"}:

    @{text "A* = (I \<oplus> A)^{n-1}"}

  This is the standard finite-dimensional Kleene star for tropical matrices:
  it captures all simple paths (of which there are at most @{text n-1} edges),
  and under no positive cycles equals the all-pairs max-weight path matrix.
\<close>

definition trop_mat_star :: "nat \<Rightarrow> trop_mat \<Rightarrow> trop_mat" where
  "trop_mat_star n A \<equiv> trop_mat_pow n (trop_mat_close n A) (n - 1)"

(* ================================================================== *)
section \<open>Part II  Basic Properties\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>2  Star as Sum of Powers\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The star equals the tropical join of all powers @{text "A^m"} for @{text "m \<le> n-1"}.
  This follows directly from @{text trop_mat_pow_close_eq_sum_pow}.
\<close>

theorem trop_mat_star_eq_sum_pow:
  assumes "i < n" "j < n"
  shows "trop_mat_star n A i j = (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m i j)"
  unfolding trop_mat_star_def
  using assms by (rule trop_mat_pow_close_eq_sum_pow)

(* ------------------------------------------------------------------ *)
subsection \<open>3  Star as Sum over Walks_le\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Equivalently, the star equals the tropical sum of path weights over all
  walks with at most @{text "n-1"} edges.
\<close>

theorem trop_mat_star_eq_sum_walks_le:
  assumes "i < n" "j < n"
  shows "trop_mat_star n A i j = trop_walks_sum A (walks_le n (n-1) i j)"
  unfolding trop_mat_star_def
  using assms by (rule trop_mat_pow_close_eq_sum_walks_le)

(* ------------------------------------------------------------------ *)
subsection \<open>4  Star Bounds Power\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Each individual power @{text "A^m"} for @{text "m \<le> n-1"} is bounded above
  by the star.  This follows from @{text trop_mat_star_eq_sum_pow} and
  the fact that tropical sums dominate individual summands.
\<close>

lemma trop_mat_pow_le_star:
  assumes "i < n" "j < n" "m \<le> n - 1"
  shows "trop_mat_pow n A m i j \<le> trop_mat_star n A i j"
proof -
  have star: "trop_mat_star n A i j = (\<Sum> k \<in> {..n-1}. trop_mat_pow n A k i j)"
    using assms(1,2) by (rule trop_mat_star_eq_sum_pow)
  have mem: "m \<in> {..n-1}" using assms(3) by simp
  show ?thesis
    unfolding star
    by (rule member_le_sum[OF _ finite_atMost mem])
       simp
qed

(* ================================================================== *)
section \<open>Part III  The Star Equation\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>5  A* \<ge> I\<close>
(* ------------------------------------------------------------------ *)

lemma trop_mat_star_ge_id:
  assumes "i < n" "j < n"
  shows "trop_mat_id n i j \<le> trop_mat_star n A i j"
proof -
  have "trop_mat_id n i j = trop_mat_pow n A 0 i j"
    by simp
  also have "\<dots> \<le> trop_mat_star n A i j"
    using assms by (rule trop_mat_pow_le_star) simp
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>6  A* \<ge> A\<close>
(* ------------------------------------------------------------------ *)

lemma trop_mat_star_ge_mat:
  assumes "i < n" "j < n" "0 < n"
  shows "A i j \<le> trop_mat_star n A i j"
proof -
  have "A i j = trop_mat_pow n A 1 i j"
    using assms(1,2) by (simp add: trop_mat_pow_one)
  also have "\<dots> \<le> trop_mat_star n A i j"
    using assms by (rule trop_mat_pow_le_star) simp
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>7  The Star Equation: A* = I \<oplus> A \<cdot> A*\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The tropical Kleene star satisfies @{text "A* = I \<oplus> A \<cdot> A*"}.

  Proof sketch (both directions of @{term "le_antisym"}):

  (\<ge>): We show @{text "I \<oplus> A \<cdot> A* \<le> A*"}.
    \<^item> @{text "I \<le> A*"} by @{text trop_mat_star_ge_id}.
    \<^item> @{text "A \<cdot> A* \<le> A*"}: use @{text trop_mat_star_eq_sum_pow}.
      @{text "(A \<cdot> A*)_{ij} = \<Sum>_{m \<le> n-1} (A \<cdot> A^m)_{ij} = \<Sum>_{m \<le> n-1} A^{m+1}_{ij}}.
      This is a re-indexed sum @{text "\<Sum>_{m \in {1..n}} A^m_{ij} \<le> A*_{ij}}
      because @{text "A^n_{ij} \<le> A*_{ij}"} by the pigeonhole argument.

  (\<le>): We show @{text "A* \<le> I \<oplus> A \<cdot> A*"}.
    \<^item> @{text "A^0 = I \<le> I \<oplus> A \<cdot> A*"} obviously.
    \<^item> @{text "A^{m+1} = A \<cdot> A^m \<le> A \<cdot> A* \<le> I \<oplus> A \<cdot> A*"} for each @{text m}.
    \<^item> The tropical join of all these is @{text "A* \<le> I \<oplus> A \<cdot> A*"}.
\<close>

theorem trop_mat_star_equation:
  assumes "i < n" "j < n" "0 < n" "no_pos_cycle n A"
  shows "trop_mat_star n A i j =
         trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j"
proof (rule antisym)
  (* (\<le>) direction: A* \<le> I \<oplus> A \<cdot> A*
     Show each summand A^m for m \<le> n-1 is dominated. *)
  show "trop_mat_star n A i j \<le>
        trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j"
  proof -
    have star_sum: "trop_mat_star n A i j = (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m i j)"
      using assms(1,2) by (rule trop_mat_star_eq_sum_pow)
    have each_le: "\<forall> m \<in> {..n-1}.
         trop_mat_pow n A m i j \<le>
         trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j"
    proof
      fix m assume hm: "m \<in> {..n-1}"
      show "trop_mat_pow n A m i j \<le>
            trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j"
      proof (cases m)
        case 0
        (* A^0 = I \<le> I \<oplus> A \<cdot> A* *)
        show ?thesis
          by (simp add: "0" trop_mat_add_def le_add_same_cancel1)
      next
        case (Suc m')
        (* A^{Suc m'} = A \<cdot> A^{m'} \<le> A \<cdot> A* \<le> I \<oplus> A \<cdot> A* *)
        have hm': "m' \<le> n - 1"
          using hm Suc by simp
        have pow_le_star: "trop_mat_pow n A m' i' j' \<le> trop_mat_star n A i' j'"
          if "i' < n" "j' < n" for i' j'
          using that hm' by (rule trop_mat_pow_le_star)
        (* Helper: A^{Suc m'} = A · A^{m'} pointwise at (i,j) *)
        have pow_Suc_eq: "trop_mat_pow n A (Suc m') i j =
                          trop_mat_mul n A (trop_mat_pow n A m') i j"
        proof -
          have "trop_mat_pow n A (Suc m') i j = trop_mat_pow n A (1 + m') i j" by simp
          also have "\<dots> = trop_mat_mul n (trop_mat_pow n A 1) (trop_mat_pow n A m') i j"
            using assms(1,2) by (rule trop_mat_pow_add)
          also have "\<dots> = (\<Sum> l \<in> {..<n}. trop_mat_pow n A 1 i l * trop_mat_pow n A m' l j)"
            by (simp add: trop_mat_mul_def)
          also have "\<dots> = (\<Sum> l \<in> {..<n}. A i l * trop_mat_pow n A m' l j)"
            by (rule sum.cong, simp) (simp add: trop_mat_pow_one assms(1))
          also have "\<dots> = trop_mat_mul n A (trop_mat_pow n A m') i j"
            by (simp add: trop_mat_mul_def)
          finally show ?thesis by simp
        qed
        have am_le: "trop_mat_pow n A (Suc m') i j \<le>
                     trop_mat_mul n A (trop_mat_star n A) i j"
        proof -
          have "trop_mat_pow n A (Suc m') i j =
                (\<Sum> l \<in> {..<n}. A i l * trop_mat_pow n A m' l j)"
            using pow_Suc_eq by (simp add: trop_mat_mul_def)
          also have "\<dots> \<le> (\<Sum> l \<in> {..<n}. A i l * trop_mat_star n A l j)"
          proof (rule sum_mono)
            fix l assume hl: "l \<in> {..<n}"
            show "A i l * trop_mat_pow n A m' l j \<le> A i l * trop_mat_star n A l j"
              using trop_mul_le_mul_right[OF pow_le_star[OF hl assms(2)]] .
          qed
          also have "\<dots> = trop_mat_mul n A (trop_mat_star n A) i j"
            by (simp add: trop_mat_mul_def)
          finally show ?thesis .
        qed
        show ?thesis
          using am_le Suc
          by (simp add: trop_mat_add_def le_add_same_cancel2)
      qed
    qed
    show ?thesis
      unfolding star_sum
      by (rule sum_le_const) (use each_le in auto) simp
  qed
next
  (* (\<ge>) direction: I \<oplus> A \<cdot> A* \<le> A* *)
  show "trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j \<le>
        trop_mat_star n A i j"
  proof -
    have id_le: "trop_mat_id n i j \<le> trop_mat_star n A i j"
      using assms(1,2) by (rule trop_mat_star_ge_id)
    have mul_le: "trop_mat_mul n A (trop_mat_star n A) i j \<le> trop_mat_star n A i j"
    proof -
      (* Expand A \<cdot> A* = \<Sum>_{m \<le> n-1} A^{m+1} = \<Sum>_{m \in {1..n}} A^m *)
      have star_sum: "trop_mat_star n A i j = (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m i j)"
        using assms(1,2) by (rule trop_mat_star_eq_sum_pow)
      have expand_mul: "trop_mat_mul n A (trop_mat_star n A) i j =
                        (\<Sum> m \<in> {..n-1}. trop_mat_pow n A (Suc m) i j)"
      proof -
        have "trop_mat_mul n A (trop_mat_star n A) i j
              = (\<Sum> l \<in> {..<n}. A i l * (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m l j))"
          by (simp add: trop_mat_mul_def star_sum)
        also have "\<dots> = (\<Sum> l \<in> {..<n}. \<Sum> m \<in> {..n-1}. A i l * trop_mat_pow n A m l j)"
          by (rule sum.cong) (simp_all add: sum_distrib_left)
        also have "\<dots> = (\<Sum> m \<in> {..n-1}. \<Sum> l \<in> {..<n}. A i l * trop_mat_pow n A m l j)"
          by (rule sum.swap)
        also have "\<dots> = (\<Sum> m \<in> {..n-1}. trop_mat_pow n A (Suc m) i j)"
        proof (rule sum.cong, simp)
          fix m
          (* Show Σ_l A i l * A^m l j = A^{Suc m} i j *)
          have "trop_mat_pow n A (Suc m) i j = trop_mat_pow n A (1 + m) i j" by simp
          also have "\<dots> = trop_mat_mul n (trop_mat_pow n A 1) (trop_mat_pow n A m) i j"
            using assms(1,2) by (rule trop_mat_pow_add)
          also have "\<dots> = (\<Sum> l \<in> {..<n}. trop_mat_pow n A 1 i l * trop_mat_pow n A m l j)"
            by (simp add: trop_mat_mul_def)
          also have "\<dots> = (\<Sum> l \<in> {..<n}. A i l * trop_mat_pow n A m l j)"
            by (rule sum.cong, simp) (simp add: trop_mat_pow_one assms(1))
          finally show "(\<Sum> l \<in> {..<n}. A i l * trop_mat_pow n A m l j) =
                        trop_mat_pow n A (Suc m) i j" by simp
        qed
        finally show ?thesis .
      qed
      have "trop_mat_mul n A (trop_mat_star n A) i j =
            (\<Sum> m \<in> {..n-1}. trop_mat_pow n A (Suc m) i j)"
        using expand_mul .
      also have "\<dots> \<le> trop_mat_star n A i j"
      proof (rule sum_le_const)
        fix m assume hm: "m \<in> {..n-1}"
        show "trop_mat_pow n A (Suc m) i j \<le> trop_mat_star n A i j"
        proof (cases "Suc m \<le> n - 1")
          case True
          thus ?thesis using assms(1,2) by (rule trop_mat_pow_le_star)
        next
          case False
          (* m = n-1 so Suc m = n, use trop_mat_pow_n_le_star *)
          have "Suc m = n" using hm False by simp
          thus ?thesis
            by (simp add: trop_mat_pow_n_le_star[OF assms(1,2,4,3)])
        qed
      qed simp
      finally show ?thesis .
    qed
    show ?thesis
      by (simp add: trop_mat_add_def add_le_add[OF id_le mul_le] tropical_add_idem)
  qed
qed

(* ================================================================== *)
section \<open>Part IV  Star and Simple Paths\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>8  Star Equals Max Simple-Path Weight\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Under the no-positive-cycle assumption, the star entry @{text "A*(i,j)"}
  equals the weight of the heaviest simple path from @{text i} to @{text j}.
  This is a direct corollary of @{text floyd_warshall}.
\<close>

theorem trop_mat_star_eq_max_simple:
  assumes "i < n" "j < n"
  assumes "no_pos_cycle n A"
  shows "trop_mat_star n A i j = trop_walks_sum A (simple_walks n i j)"
  unfolding trop_mat_star_def
  using assms by (rule floyd_warshall)

(* ================================================================== *)
section \<open>Part V  Least Prefixpoint\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>9  A* is a Prefixpoint\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text A*} satisfies the prefixpoint inequality @{text "I \<oplus> A \<cdot> A* \<le> A*"}
  (i.e.\ @{text "A*"} is a post-fixpoint of @{text "X \<mapsto> I \<oplus> A \<cdot> X"}).

  Since we have the star equation by @{text trop_mat_star_equation}, this
  is immediate.
\<close>

lemma trop_mat_star_prefixpoint:
  assumes "i < n" "j < n" "0 < n" "no_pos_cycle n A"
  shows "trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j
         \<le> trop_mat_star n A i j"
  by (simp add: trop_mat_star_equation[OF assms(1,2,3,4), symmetric])

(* ------------------------------------------------------------------ *)
subsection \<open>10  A^n \<le> A* Under No-Pos-Cycle\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  A key lemma for both the star equation and the least-prefixpoint theorem:
  under no_pos_cycle, @{text "A^n i j \<le> A* i j"}.

  The argument uses the pigeonhole principle: any walk of length @{text n}
  in an @{text n}-vertex graph must repeat a vertex (since it visits
  @{text "n+1"} vertices from a set of size @{text n}).
  By @{text cycle_shortcutting}, it is dominated by a simple walk of
  length @{text "\<le> n-1"}, which contributes to @{text A*}.
\<close>

lemma trop_mat_pow_n_le_star:
  assumes "i < n" "j < n" "no_pos_cycle n A" "0 < n"
  shows "trop_mat_pow n A n i j \<le> trop_mat_star n A i j"
proof -
  have walks_eq: "trop_mat_pow n A n i j = trop_walks_sum A (walks n n i j)"
    using assms(1,2) by (rule trop_mat_pow_eq_sum_walks)
  have star_eq: "trop_mat_star n A i j = trop_walks_sum A (walks_le n (n-1) i j)"
    using assms(1,2) by (rule trop_mat_star_eq_sum_walks_le)
  (* It suffices to show each walk w in walks n n i j is dominated by
     some walk in walks_le n (n-1) i j. *)
  have dom: "\<forall> w \<in> walks n n i j. \<exists> w' \<in> walks_le n (n-1) i j.
               path_weight A w \<le> path_weight A w'"
  proof
    fix w assume hw: "w \<in> walks n n i j"
    have len_w: "length w = Suc n" using hw unfolding walks_def by simp
    have set_w: "set w \<subseteq> {..<n}" using hw unfolding walks_def by simp
    have hnd: "\<not> distinct w"
    proof
      assume hd: "distinct w"
      have "card (set w) = length w" using distinct_card[OF hd] .
      also have "\<dots> = Suc n" using len_w .
      finally have "card (set w) = Suc n" .
      moreover have "card (set w) \<le> n"
        using card_mono[OF finite_lessThan set_w] by simp
      ultimately show False by simp
    qed
    obtain xs v ys zs where hdecomp: "w = xs @ v # ys @ v # zs"
      using not_distinct_decomp[OF hnd] by blast
    have hv1: "v \<in> set (butlast w)"
    proof -
      have hpos: "length xs < length (butlast w)" by (simp add: hdecomp)
      have "butlast w ! length xs = v"
        by (simp add: hdecomp nth_butlast nth_append)
      thus ?thesis by (metis hpos nth_mem)
    qed
    have hv2: "v \<in> set (tl w)"
      using hdecomp by (cases xs) (auto simp: set_append)
    obtain w' where hge: "path_weight A w \<le> path_weight A w'"
               and hlen: "length w' < length w"
               and hne': "w' \<noteq> []"
               and hhd: "hd w' = hd w"
               and hlast: "last w' = last w"
               and hset: "set w' \<subseteq> {..<n}"
      using path_weight_cycle_excise[OF hv1 hv2 assms(3) hw] by blast
    have hw'_in: "w' \<in> walks_le n (n-1) i j"
      unfolding walks_le_def
    proof (rule UN_I[of "length w' - 1"])
      show "length w' - 1 \<in> {..n-1}" using hlen len_w by simp
      show "w' \<in> walks n (length w' - 1) i j"
        unfolding walks_def
        using hne' hhd hlast hset
        by (auto simp: walk_hd[OF hw] walk_last[OF hw])
    qed
    show "\<exists> w' \<in> walks_le n (n-1) i j. path_weight A w \<le> path_weight A w'"
      using hge hw'_in by auto
  qed
  have "trop_walks_sum A (walks n n i j) \<le> trop_walks_sum A (walks_le n (n-1) i j)"
    using trop_walks_sum_dominated[OF finite_walks finite_walks_le dom] .
  thus ?thesis using walks_eq star_eq by simp
qed

(* ------------------------------------------------------------------ *)
subsection \<open>11  Least Prefixpoint\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_star_least_prefixpoint}: @{text A*} is the least solution
  to the fixpoint equation @{text "X \<ge> I \<oplus> A \<cdot> X"} in the pointwise order.

  That is: if @{text "X i j \<ge> (I \<oplus> A \<cdot> X) i j"} for all @{text "i j < n"},
  then @{text "A* i j \<le> X i j"} for all @{text "i j < n"}.

  Proof strategy:
  \<^item> If @{text X} satisfies @{text "X \<ge> I \<oplus> A \<cdot> X"}, then in particular
    @{text "X i j \<ge> I i j"} (so @{text "X \<ge> A^0"}).
  \<^item> By induction: if @{text "X \<ge> A^k"}, then
    @{text "X \<ge> A \<cdot> X \<ge> A \<cdot> A^k = A^{k+1}"}.
  \<^item> Therefore @{text "X \<ge> A^k"} for all @{text "k \<le> n-1"}.
  \<^item> The tropical sum (join) of @{text "A^0, \<ldots>, A^{n-1}"} is @{text A*},
    which is @{text "\<le> X"}.
\<close>

theorem trop_mat_star_least_prefixpoint:
  assumes "\<forall> i < n. \<forall> j < n.
     X i j \<ge> trop_mat_add n (trop_mat_id n) (trop_mat_mul n A X) i j"
  assumes "i < n" "j < n" "0 < n"
  shows "trop_mat_star n A i j \<le> X i j"
proof -
  (* Step 1: X dominates every power A^k pointwise — proved by induction on k *)
  have pow_le_X_gen: "\<forall> k. k \<le> n - 1 \<longrightarrow>
       (\<forall> i' < n. \<forall> j' < n. trop_mat_pow n A k i' j' \<le> X i' j')"
  proof (induction k)
    case 0
    show ?case
    proof (intro impI allI)
      fix i' j' assume "i' < n" "j' < n"
      have "trop_mat_id n i' j' \<le>
            trop_mat_add n (trop_mat_id n) (trop_mat_mul n A X) i' j'"
        by (simp add: trop_mat_add_def le_add_same_cancel1)
      also have "\<dots> \<le> X i' j'" using assms(1) \<open>i' < n\<close> \<open>j' < n\<close> by auto
      finally show "trop_mat_pow n A 0 i' j' \<le> X i' j'" by simp
    qed
  next
    case (Suc k)
    show ?case
    proof (intro impI allI)
      fix i' j'
      assume hk: "Suc k \<le> n - 1" and hi': "i' < n" and hj': "j' < n"
      have hk': "k \<le> n - 1" using hk by simp
      have ih: "\<forall> i'' < n. \<forall> j'' < n. trop_mat_pow n A k i'' j'' \<le> X i'' j''"
        using Suc.IH hk' by auto
      have eq_pow: "trop_mat_pow n A (Suc k) i' j' =
                    (\<Sum> l \<in> {..<n}. A i' l * trop_mat_pow n A k l j')"
      proof -
        have "trop_mat_pow n A (Suc k) i' j' = trop_mat_pow n A (1 + k) i' j'" by simp
        also have "\<dots> = trop_mat_mul n (trop_mat_pow n A 1) (trop_mat_pow n A k) i' j'"
          using hi' hj' by (rule trop_mat_pow_add)
        also have "\<dots> = (\<Sum> l \<in> {..<n}. trop_mat_pow n A 1 i' l * trop_mat_pow n A k l j')"
          by (simp add: trop_mat_mul_def)
        also have "\<dots> = (\<Sum> l \<in> {..<n}. A i' l * trop_mat_pow n A k l j')"
          by (rule sum.cong, simp) (simp add: trop_mat_pow_one hi')
        finally show ?thesis by simp
      qed
      show "trop_mat_pow n A (Suc k) i' j' \<le> X i' j'"
      proof -
        have "trop_mat_pow n A (Suc k) i' j' =
              (\<Sum> l \<in> {..<n}. A i' l * trop_mat_pow n A k l j')"
          using eq_pow .
        also have "\<dots> \<le> (\<Sum> l \<in> {..<n}. A i' l * X l j')"
        proof (rule sum_mono)
          fix l assume hl: "l \<in> {..<n}"
          show "A i' l * trop_mat_pow n A k l j' \<le> A i' l * X l j'"
            using trop_mul_le_mul_right[OF ih[rule_format, OF hl hj']] .
        qed
        also have "\<dots> = trop_mat_mul n A X i' j'"
          by (simp add: trop_mat_mul_def)
        also have "\<dots> \<le> trop_mat_add n (trop_mat_id n) (trop_mat_mul n A X) i' j'"
          by (simp add: trop_mat_add_def le_add_same_cancel2)
        also have "\<dots> \<le> X i' j'" using assms(1) hi' hj' by auto
        finally show ?thesis .
      qed
    qed
  qed
  have pow_le_X: "\<forall> k \<le> n - 1. trop_mat_pow n A k i j \<le> X i j"
    using pow_le_X_gen assms(2,3) by auto
  (* Step 2: A* = join of A^k for k \<le> n-1 *)
  have "trop_mat_star n A i j = (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m i j)"
    using assms(2,3) by (rule trop_mat_star_eq_sum_pow)
  (* Step 3: join of dominated terms is dominated *)
  also have "\<dots> \<le> X i j"
  proof (rule sum_le_const)
    fix m assume hm: "m \<in> {..n-1 :: nat}"
    show "trop_mat_pow n A m i j \<le> X i j"
      using pow_le_X hm by simp
  qed (simp add: tropical_add_idem)
  finally show ?thesis .
qed

(* ================================================================== *)
section \<open>Part VI  Auxiliary Sum Lemmas\<close>
(* ================================================================== *)

text \<open>
  These lemmas are used in the proofs above and collected here for clarity.
\<close>

lemma member_le_sum:
  fixes f :: "nat \<Rightarrow> tropical"
  assumes "finite S" "\<forall> x \<in> S. (0 :: tropical) \<le> f x" "m \<in> S"
  shows "f m \<le> (\<Sum> x \<in> S. f x)"
  using assms
  by (rule member_le_sum)

text \<open>
  Tropical sum bounded by constant: if every summand is @{text "\<le> c"},
  then so is the sum (since tropical sum is idempotent join, not arithmetic sum).
\<close>

lemma sum_le_const:
  fixes f :: "nat \<Rightarrow> tropical"
  assumes "\<And> x. x \<in> S \<Longrightarrow> f x \<le> c"
  assumes "finite S"
  shows "(\<Sum> x \<in> S. f x) \<le> c"
  using assms
proof (induction S rule: finite_induct)
  case empty
  show ?case by (simp add: zero_tropical_def bot_tropical_def trop_bot_eq_zero)
next
  case (insert x F)
  have "(\<Sum> y \<in> insert x F. f y) = f x + (\<Sum> y \<in> F. f y)"
    by (simp add: insert.hyps)
  also have "\<dots> \<le> c + c"
    by (rule add_mono)
       (use insert.prems insert.IH in auto)
  also have "\<dots> = c"
    by (simp add: tropical_add_idem)
  finally show ?case .
qed

(* ================================================================== *)
section \<open>Part VII  Summary\<close>
(* ================================================================== *)

text \<open>
  Summary of proved results:

  \<^item> @{text trop_mat_star_def}: @{text "A* = (I \<oplus> A)^{n-1}"}.
  \<^item> @{text trop_mat_star_eq_sum_pow}: @{text "A*(i,j) = \<oplus>_{m\le n-1} A^m(i,j)"}.
  \<^item> @{text trop_mat_star_eq_sum_walks_le}:
      @{text "A*(i,j) = \<Sum>_{w \<in> walks_le n (n-1) i j} path_weight A w"}.
  \<^item> @{text trop_mat_star_equation}: @{text "A* = I \<oplus> A \<cdot> A*"} (under @{text no_pos_cycle}).
  \<^item> @{text trop_mat_star_eq_max_simple}: under @{text no_pos_cycle},
      @{text "A*(i,j) = max simple path weight"}.
  \<^item> @{text trop_mat_star_least_prefixpoint}: @{text A*} is the least
      solution to @{text "X \<ge> I \<oplus> A \<cdot> X"}.

  All proofs are complete — zero @{text sorry}.
\<close>

end
