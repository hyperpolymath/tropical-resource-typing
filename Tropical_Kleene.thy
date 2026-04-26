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
    walks of at most @{text "n-1"} edges.
  \<^item> @{text trop_mat_star_equation}: @{text "A* = I \<oplus> A \<cdot> A*"}
    (the star equation / Bellman equation).
  \<^item> @{text trop_mat_star_eq_max_simple}: under no_pos_cycle,
    @{text "A*(i,j)"} equals the max-weight simple-path weight.
  \<^item> @{text trop_mat_star_least_prefixpoint}: @{text "A*"} is the least
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
  it captures all simple paths (of which there are at most @{text "n-1"} edges),
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

(* member_le_sum / sum_le_const are forward-needed by trop_mat_pow_le_star
   and other proofs in this section.  Hoisted here so Isabelle 2025-1
   accepts the references (sequential parsing forbids forward refs). *)

lemma member_le_sum:
  fixes f :: "nat \<Rightarrow> tropical"
  assumes "finite S" "\<forall> x \<in> S. (0 :: tropical) \<le> f x" "m \<in> S"
  shows "f m \<le> (\<Sum> x \<in> S. f x)"
proof -
  have decomp: "(\<Sum> x \<in> S. f x) = f m + (\<Sum> x \<in> S - {m}. f x)"
    using assms(1,3) by (subst sum.remove) auto
  have "f m + (\<Sum> x \<in> S. f x) = f m + (f m + (\<Sum> x \<in> S - {m}. f x))"
    using decomp by simp
  also have "\<dots> = (f m + f m) + (\<Sum> x \<in> S - {m}. f x)"
    by (simp add: add.assoc)
  also have "\<dots> = f m + (\<Sum> x \<in> S - {m}. f x)"
    by (simp add: tropical_add_idem)
  also have "\<dots> = (\<Sum> x \<in> S. f x)" using decomp by simp
  finally have "f m + (\<Sum> x \<in> S. f x) = (\<Sum> x \<in> S. f x)" .
  thus ?thesis by (simp add: trop_add_le_iff)
qed

lemma sum_le_const:
  fixes f :: "'a \<Rightarrow> tropical"
  assumes hbound: "\<And> x. x \<in> S \<Longrightarrow> f x \<le> c"
  assumes hfin: "finite S"
  shows "(\<Sum> x \<in> S. f x) \<le> c"
  using hfin hbound
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

lemma trop_mat_pow_le_star:
  assumes "i < n" "j < n" "m \<le> n - 1"
  shows "trop_mat_pow n A m i j \<le> trop_mat_star n A i j"
proof -
  have star: "trop_mat_star n A i j = (\<Sum> k \<in> {..n-1}. trop_mat_pow n A k i j)"
    using assms(1,2) by (rule trop_mat_star_eq_sum_pow)
  have mem: "m \<in> {..n-1}" using assms(3) by simp
  show ?thesis
    unfolding star
  proof -
    let ?f = "\<lambda>k. trop_mat_pow n A k i j"
    have decomp: "(\<Sum> k \<in> {..n-1}. ?f k) = ?f m + (\<Sum> k \<in> {..n-1}-{m}. ?f k)"
      using mem by (subst sum.remove[OF finite_atMost mem]) auto
    have "?f m + (\<Sum> k \<in> {..n-1}. ?f k)
          = ?f m + (?f m + (\<Sum> k \<in> {..n-1}-{m}. ?f k))" using decomp by simp
    also have "\<dots> = (?f m + ?f m) + (\<Sum> k \<in> {..n-1}-{m}. ?f k)"
      by (simp add: add.assoc)
    also have "\<dots> = ?f m + (\<Sum> k \<in> {..n-1}-{m}. ?f k)"
      by (simp add: tropical_add_idem)
    also have "\<dots> = (\<Sum> k \<in> {..n-1}. ?f k)" using decomp by simp
    finally have "?f m + (\<Sum> k \<in> {..n-1}. ?f k) = (\<Sum> k \<in> {..n-1}. ?f k)" .
    thus "?f m \<le> (\<Sum> k \<in> {..n-1}. ?f k)" by (simp add: trop_add_le_iff)
  qed
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
  assumes "i < n" "j < n" "1 < n"
  shows "A i j \<le> trop_mat_star n A i j"
proof -
  have "A i j = trop_mat_pow n A 1 i j"
    using assms(1,2) trop_mat_pow_one[OF assms(1,2)] by simp
  also have "\<dots> \<le> trop_mat_star n A i j"
    using assms(1,2) by (rule trop_mat_pow_le_star) (use assms(3) in linarith)
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
      @{text "(A . A*)_{ij} = SUM_{m <= n-1} (A . A^m)_{ij} = SUM_{m <= n-1} A^{m+1}_{ij}"}.
      This is a re-indexed sum @{text "SUM_{m in {1..n}} A^m_{ij} <= A*_{ij}"}
      because @{text "A^n_{ij} \<le> A*_{ij}"} by the pigeonhole argument.

  (\<le>): We show @{text "A* \<le> I \<oplus> A \<cdot> A*"}.
    \<^item> @{text "A^0 = I \<le> I \<oplus> A \<cdot> A*"} obviously.
    \<^item> @{text "A^{m+1} = A \<cdot> A^m \<le> A \<cdot> A* \<le> I \<oplus> A \<cdot> A*"} for each @{text m}.
    \<^item> The tropical join of all these is @{text "A* \<le> I \<oplus> A \<cdot> A*"}.
\<close>

(* trop_mat_pow_n_le_star hoisted above trop_mat_star_equation
   so the (\<le>) direction can use it without forward-reference. *)

lemma trop_mat_pow_n_le_star:
  assumes "i < n" "j < n" "no_pos_cycle n A" "0 < n"
  shows "trop_mat_pow n A n i j \<le> trop_mat_star n A i j"
proof -
  have walks_eq: "trop_mat_pow n A n i j = trop_walks_sum A (walks n n i j)"
    using assms(1,2) by (rule trop_mat_pow_eq_sum_walks)
  have star_eq: "trop_mat_star n A i j = trop_walks_sum A (walks_le n (n-1) i j)"
    using assms(1,2) by (rule trop_mat_star_eq_sum_walks_le)
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
    obtain w' where hge: "path_weight A w \<le> path_weight A w'"
               and hw'_simple: "w' \<in> simple_walks n i j"
      using cycle_shortcutting[OF assms(3) hw] by blast
    from hw'_simple obtain m where hw'_m: "w' \<in> walks n m i j"
      and hw'_dist: "distinct w'"
      unfolding simple_walks_def by auto
    have hne': "w' \<noteq> []" using hw'_m unfolding walks_def by auto
    have hset:  "set w' \<subseteq> {..<n}" using walk_vertices_bounded[OF hw'_m] .
    have hlen_n: "length w' \<le> n"
    proof -
      have "length w' = card (set w')" using distinct_card[OF hw'_dist, symmetric] .
      also have "card (set w') \<le> card {..<n}"
        using card_mono[OF finite_lessThan hset] .
      finally show ?thesis by simp
    qed
    have hw'_in: "w' \<in> walks_le n (n-1) i j"
      unfolding walks_le_def
    proof (rule UN_I[of "length w' - 1"])
      show "length w' - 1 \<in> {..n-1}" using hlen_n hne' by (cases w') auto
      have hm: "m = length w' - 1" using hw'_m unfolding walks_def by auto
      show "w' \<in> walks n (length w' - 1) i j" using hw'_m hm by simp
    qed
    show "\<exists> w' \<in> walks_le n (n-1) i j. path_weight A w \<le> path_weight A w'"
      using hge hw'_in by auto
  qed
  have "trop_walks_sum A (walks n n i j) \<le> trop_walks_sum A (walks_le n (n-1) i j)"
    using trop_walks_sum_dominated[OF finite_walks finite_walks_le dom] .
  thus ?thesis using walks_eq star_eq by simp
qed

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
        (* A^0 = I \<le> I \<oplus> A \<cdot> A*; in tropical (max), x \<le> x + y always. *)
        let ?I = "trop_mat_id n i j"
        let ?X = "trop_mat_mul n A (trop_mat_star n A) i j"
        have idem_step: "?I + (?I + ?X) = ?I + ?X"
          by (simp add: add.assoc[symmetric] tropical_add_idem)
        hence "?I \<le> ?I + ?X" by (simp add: trop_add_le_iff)
        thus ?thesis using "0" by (simp add: trop_mat_add_def)
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
          proof (rule sum.cong[OF refl])
            fix l assume "l \<in> {..<n}"
            hence hl: "l < n" by simp
            have "trop_mat_pow n A 1 i l = A i l"
              using trop_mat_pow_one[OF assms(1) hl] .
            thus "trop_mat_pow n A 1 i l * trop_mat_pow n A m' l j =
                  A i l * trop_mat_pow n A m' l j" by simp
          qed
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
            hence hln: "l < n" by simp
            show "A i l * trop_mat_pow n A m' l j \<le> A i l * trop_mat_star n A l j"
              using trop_mul_le_mul_right[OF pow_le_star[OF hln assms(2)]] .
          qed
          also have "\<dots> = trop_mat_mul n A (trop_mat_star n A) i j"
            by (simp add: trop_mat_mul_def)
          finally show ?thesis .
        qed
        show ?thesis
        proof -
          let ?I = "trop_mat_id n i j"
          let ?A = "trop_mat_pow n A (Suc m') i j"
          let ?S = "trop_mat_mul n A (trop_mat_star n A) i j"
          have hle: "?A \<le> ?S" using am_le by simp
          have h1: "?A + ?S = ?S" using hle by (simp add: trop_add_le_iff)
          have step: "?A + (?I + ?S) = ?I + ?S"
          proof -
            have "?A + (?I + ?S) = ?I + (?A + ?S)" by (simp add: ac_simps)
            also have "\<dots> = ?I + ?S" using h1 by simp
            finally show ?thesis .
          qed
          have hAle: "?A \<le> ?I + ?S" using step by (simp add: trop_add_le_iff)
          show ?thesis using hAle Suc by (simp add: trop_mat_add_def)
        qed
      qed
    qed
    show ?thesis
      unfolding star_sum
    proof (rule sum_le_const)
      fix m assume "m \<in> {..n-1}"
      thus "trop_mat_pow n A m i j \<le>
            trop_mat_add n (trop_mat_id n) (trop_mat_mul n A (trop_mat_star n A)) i j"
        using each_le by auto
    next
      show "finite {..n-1}" by simp
    qed
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
              = (\<Sum> l \<in> {..<n}. A i l * trop_mat_star n A l j)"
          by (simp add: trop_mat_mul_def)
        also have "\<dots> = (\<Sum> l \<in> {..<n}. A i l * (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m l j))"
        proof (rule sum.cong[OF refl])
          fix l assume "l \<in> {..<n}"
          hence hl: "l < n" by simp
          have "trop_mat_star n A l j = (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m l j)"
            using trop_mat_star_eq_sum_pow[OF hl assms(2)] .
          thus "A i l * trop_mat_star n A l j =
                A i l * (\<Sum> m \<in> {..n-1}. trop_mat_pow n A m l j)" by simp
        qed
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
          proof (rule sum.cong[OF refl])
            fix l assume "l \<in> {..<n}"
            hence hl: "l < n" by simp
            have "trop_mat_pow n A 1 i l = A i l"
              using trop_mat_pow_one[OF assms(1) hl] .
            thus "trop_mat_pow n A 1 i l * trop_mat_pow n A m l j =
                  A i l * trop_mat_pow n A m l j" by simp
          qed
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
          show ?thesis using trop_mat_pow_le_star[OF assms(1) assms(2) True] .
        next
          case False
          (* m = n-1 so Suc m = n, use trop_mat_pow_n_le_star *)
          have "Suc m = n" using hm False assms(3) by simp
          thus ?thesis
            by (simp add: trop_mat_pow_n_le_star[OF assms(1,2,4,3)])
        qed
      qed simp
      finally show ?thesis .
    qed
    show ?thesis
    proof -
      have "trop_mat_id n i j + trop_mat_mul n A (trop_mat_star n A) i j
            \<le> trop_mat_star n A i j + trop_mat_star n A i j"
        using add_mono[OF id_le mul_le] .
      also have "\<dots> = trop_mat_star n A i j" by (simp add: tropical_add_idem)
      finally have "trop_mat_id n i j + trop_mat_mul n A (trop_mat_star n A) i j
            \<le> trop_mat_star n A i j" .
      thus ?thesis by (simp add: trop_mat_add_def)
    qed
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
  @{text "A*"} satisfies the prefixpoint inequality @{text "I \<oplus> A \<cdot> A* \<le> A*"}
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

(* trop_mat_pow_n_le_star moved earlier (above trop_mat_star_equation)
   to avoid forward-reference rejected by Isabelle 2025-1. *)

(* ------------------------------------------------------------------ *)
subsection \<open>11  Least Prefixpoint\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_star_least_prefixpoint}: @{text "A*"} is the least solution
  to the fixpoint equation @{text "X \<ge> I \<oplus> A \<cdot> X"} in the pointwise order.

  That is: if @{text "X i j \<ge> (I \<oplus> A \<cdot> X) i j"} for all @{text "i j < n"},
  then @{text "A* i j \<le> X i j"} for all @{text "i j < n"}.

  Proof strategy:
  \<^item> If @{text X} satisfies @{text "X \<ge> I \<oplus> A \<cdot> X"}, then in particular
    @{text "X i j \<ge> I i j"} (so @{text "X \<ge> A^0"}).
  \<^item> By induction: if @{text "X \<ge> A^k"}, then
    @{text "X \<ge> A \<cdot> X \<ge> A \<cdot> A^k = A^{k+1}"}.
  \<^item> Therefore @{text "X \<ge> A^k"} for all @{text "k \<le> n-1"}.
  \<^item> The tropical sum (join) of @{text "A^0, \<ldots>, A^{n-1}"} is @{text "A*"},
    which is @{text "\<le> X"}.
\<close>

theorem trop_mat_star_least_prefixpoint:
  assumes "\<forall> i < n. \<forall> j < n.
     X i j \<ge> trop_mat_add n (trop_mat_id n) (trop_mat_mul n A X) i j"
  assumes "i < n" "j < n" "0 < n"
  shows "trop_mat_star n A i j \<le> X i j"
proof -
  (* Step 1: X dominates every power A^k pointwise — proved by induction on k *)
  have pow_le_X_gen: "k \<le> n - 1 \<longrightarrow>
       (\<forall> i' < n. \<forall> j' < n. trop_mat_pow n A k i' j' \<le> X i' j')" for k
  proof (induction k)
    case 0
    show ?case
    proof (intro impI allI)
      fix i' j' assume "i' < n" "j' < n"
      have step: "trop_mat_id n i' j' + (trop_mat_id n i' j' + trop_mat_mul n A X i' j')
                  = trop_mat_id n i' j' + trop_mat_mul n A X i' j'"
        by (simp add: add.assoc[symmetric] tropical_add_idem)
      have "trop_mat_id n i' j' \<le>
            trop_mat_id n i' j' + trop_mat_mul n A X i' j'"
        using step by (simp add: trop_add_le_iff)
      hence "trop_mat_id n i' j' \<le>
            trop_mat_add n (trop_mat_id n) (trop_mat_mul n A X) i' j'"
        by (simp add: trop_mat_add_def)
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
        proof (rule sum.cong[OF refl])
          fix l assume "l \<in> {..<n}"
          hence hl: "l < n" by simp
          have "trop_mat_pow n A 1 i' l = A i' l"
            using trop_mat_pow_one[OF hi' hl] .
          thus "trop_mat_pow n A 1 i' l * trop_mat_pow n A k l j' =
                A i' l * trop_mat_pow n A k l j'" by simp
        qed
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
          hence hln: "l < n" by simp
          show "A i' l * trop_mat_pow n A k l j' \<le> A i' l * X l j'"
            using trop_mul_le_mul_right[OF ih[rule_format, OF hln hj']] .
        qed
        also have "\<dots> = trop_mat_mul n A X i' j'"
          by (simp add: trop_mat_mul_def)
        also have "\<dots> \<le> trop_mat_add n (trop_mat_id n) (trop_mat_mul n A X) i' j'"
        proof -
          let ?a = "trop_mat_mul n A X i' j'"
          let ?b = "trop_mat_id n i' j'"
          have step: "?a + (?b + ?a) = ?b + ?a"
          proof -
            have "?a + (?b + ?a) = ?b + (?a + ?a)" by (simp add: ac_simps)
            also have "\<dots> = ?b + ?a" by (simp add: tropical_add_idem)
            finally show ?thesis .
          qed
          have "?a \<le> ?b + ?a" using step by (simp add: trop_add_le_iff)
          thus ?thesis by (simp add: trop_mat_add_def)
        qed
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

(* member_le_sum / sum_le_const moved earlier in file (before
   trop_mat_pow_le_star) so Isabelle 2025-1 sees them at first use. *)

(* ================================================================== *)
section \<open>Part VII  Summary\<close>
(* ================================================================== *)

text \<open>
  Summary of proved results:

  \<^item> @{text trop_mat_star_def}: @{text "A* = (I \<oplus> A)^{n-1}"}.
  \<^item> @{text trop_mat_star_eq_sum_pow}: @{text "A*(i,j) = \<oplus>_{m \<le> n-1} A^m(i,j)"}.
  \<^item> @{text trop_mat_star_eq_sum_walks_le}:
      @{text "A*(i,j) = \<Sum>_{w \<in> walks_le n (n-1) i j} path_weight A w"}.
  \<^item> @{text trop_mat_star_equation}: @{text "A* = I \<oplus> A \<cdot> A*"} (under @{text no_pos_cycle}).
  \<^item> @{text trop_mat_star_eq_max_simple}: under @{text no_pos_cycle},
      @{text "A*(i,j) = max simple path weight"}.
  \<^item> @{text trop_mat_star_least_prefixpoint}: @{text "A*"} is the least
      solution to @{text "X \<ge> I \<oplus> A \<cdot> X"}.

  All proofs are complete — zero @{text sorry}.
\<close>

end
