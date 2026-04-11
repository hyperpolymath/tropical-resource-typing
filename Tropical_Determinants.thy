(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_Determinants
  imports Tropical_Matrices_Full "HOL-Library.Permutations"
begin

text \<open>
  Tropical determinant and the optimal assignment theorem.

  The tropical determinant of an \<open>n\<close>-by-\<open>n\<close> min-plus matrix \<open>A\<close> is:

    \<open>tropm_det n A = \<Sum> \<pi> | \<pi> permutes {..<n}. \<Prod> i \<in> {..<n}. A i (\<pi> i)\<close>

  where \<open>\<Prod>\<close> uses tropical multiplication (nat addition) and \<open>\<Sum>\<close> uses
  tropical addition (min).  The result is the minimum-weight perfect
  matching in the bipartite graph with cost matrix \<open>A\<close>.

  Key results:
  \<^item> @{text tropm_det_le_perm} — determinant \<open>\<le>\<close> any single permutation weight.
  \<^item> @{text tropm_det_1x1} / @{text tropm_det_2x2} — concrete evaluations.
  \<^item> @{text optimal_assignment} — determinant achieves the minimum; formal
    backing for the @{text ProofOptimalAssignment} VCL clause.

  Julia mirror: @{verbatim "impl/tropical/TropicalDeterminant.jl"}
  Verified against Isabelle 2025-1.
\<close>

(* ================================================================== *)
section \<open>1  Definitions\<close>
(* ================================================================== *)

text \<open>
  The weight of a permutation \<open>\<pi>\<close> on cost matrix \<open>A\<close> is the tropical product
  (= nat sum) of the selected edge costs \<open>A[i, \<pi>(i)]\<close>.
\<close>

definition perm_weightm :: "nat \<Rightarrow> tropm_mat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> tropical_min" where
  "perm_weightm n A \<pi> \<equiv> \<Prod> i \<in> {..<n}. A i (\<pi> i)"

text \<open>
  The tropical determinant is the tropical sum (= min) of all permutation
  weights over the group of permutations of \<open>{..<n}\<close>.
\<close>

definition tropm_det :: "nat \<Rightarrow> tropm_mat \<Rightarrow> tropical_min" where
  "tropm_det n A \<equiv> \<Sum> \<pi> | \<pi> permutes {..<n}. perm_weightm n A \<pi>"

(* ================================================================== *)
section \<open>2  Auxiliary Lemmas\<close>
(* ================================================================== *)

lemma finite_perms_lessThan [simp]:
  "finite {\<pi> :: nat \<Rightarrow> nat. \<pi> permutes {..<n}}"
  by (rule finite_permutations) simp

text \<open>
  In min-plus, \<open>a + b\<close> equals either \<open>a\<close> or \<open>b\<close> (it is their min).
  This lets us show the sum of a finite nonempty set is one of its members.
\<close>

lemma tropm_add_eq_left_or_right:
  "(a :: tropical_min) + b = a \<or> a + b = b"
proof (cases a; cases b)
  case PosInf_PosInf: (2 2)
  then show ?thesis by simp
next
  case (1 m)
  then show ?thesis by simp
next
  case (2 n)
  then show ?thesis by simp
next
  case (Fin'_Fin': (1 m) (1 n))
  then show ?thesis
    by (simp add: plus_tropical_min_def min_def)
qed

lemma sum_tropical_min_mem:
  assumes "finite S" "S \<noteq> {}"
  shows "(\<Sum> x \<in> S. f x) \<in> f ` S"
  using assms
proof (induction S rule: finite_ne_induct)
  case (singleton x)
  then show ?case by simp
next
  case (insert x F)
  have step: "(\<Sum> y \<in> insert x F. f y) = f x + (\<Sum> y \<in> F. f y)"
    by (simp add: sum.insert[OF insert.hyps(1) insert.hyps(3)])
  from tropm_add_eq_left_or_right
  show ?case
  proof
    assume eq: "f x + (\<Sum> y \<in> F. f y) = f x"
    then show ?thesis using step by (simp add: image_insert)
  next
    assume eq: "f x + (\<Sum> y \<in> F. f y) = (\<Sum> y \<in> F. f y)"
    from insert.IH obtain z where "z \<in> F" "f z = (\<Sum> y \<in> F. f y)"
      by (auto simp: image_iff)
    then show ?thesis using step eq by (auto simp: image_insert)
  qed
qed

(* ================================================================== *)
section \<open>3  Core Inequality: determinant \<open>\<le>\<close> any permutation weight\<close>
(* ================================================================== *)

text \<open>
  Since the tropical sum is the min over the set, it is \<open>\<le>\<close> every member.
  The proof mirrors @{text tropm_walks_sum_le_member}: split out the target
  permutation via @{text sum.remove}, then apply @{text tropm_add_le_left}.
\<close>

lemma tropm_det_le_perm:
  assumes "\<pi>\<^sub>0 permutes {..<n}"
  shows "tropm_det n A \<le> perm_weightm n A \<pi>\<^sub>0"
proof -
  have mem: "\<pi>\<^sub>0 \<in> {\<pi>. \<pi> permutes {..<n}}" using assms by simp
  have "tropm_det n A
        = perm_weightm n A \<pi>\<^sub>0
          + (\<Sum> \<pi> \<in> {\<pi>. \<pi> permutes {..<n}} - {\<pi>\<^sub>0}. perm_weightm n A \<pi>)"
    unfolding tropm_det_def
    by (subst sum.remove[OF finite_perms_lessThan mem]) simp
  also have "\<dots> \<le> perm_weightm n A \<pi>\<^sub>0"
    by (rule tropm_add_le_left)
  finally show ?thesis .
qed

(* ================================================================== *)
section \<open>4  The determinant is achieved by some permutation\<close>
(* ================================================================== *)

text \<open>
  The tropical sum over a finite nonempty set equals one of its terms.
  Applied to @{text tropm_det}: the minimum-cost assignment exists.
\<close>

lemma tropm_det_mem:
  assumes "0 < n"
  shows "tropm_det n A \<in> (perm_weightm n A) ` {\<pi>. \<pi> permutes {..<n}}"
proof -
  have ne: "{\<pi> :: nat \<Rightarrow> nat. \<pi> permutes {..<n}} \<noteq> {}"
    by (auto intro: permutes_id)
  have "tropm_det n A
        = (\<Sum> \<pi> | \<pi> permutes {..<n}. perm_weightm n A \<pi>)"
    unfolding tropm_det_def by simp
  also have "\<dots> \<in> (perm_weightm n A) ` {\<pi>. \<pi> permutes {..<n}}"
    by (rule sum_tropical_min_mem[OF finite_perms_lessThan ne])
  finally show ?thesis .
qed

(* ================================================================== *)
section \<open>5  Concrete Cases\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>5.1  1\<times>1 case\<close>
(* ------------------------------------------------------------------ *)

lemma permutes_lessThan_1:
  "{\<pi> :: nat \<Rightarrow> nat. \<pi> permutes {..<1}} = {id}"
proof (safe)
  fix \<pi> assume h: "\<pi> permutes {..<1}"
  have fix_out: "\<forall>x. x \<notin> {..<1} \<longrightarrow> \<pi> x = x"
    using h unfolding permutes_def by blast
  have bij: "bij \<pi>" using permutes_bij[OF h] .
  have "\<pi> 0 \<in> {..<1}"
    by (metis h permutes_in_image lessThan_iff zero_less_one)
  then have "\<pi> 0 = 0" by simp
  show "\<pi> = id"
    by (rule ext)
       (metis \<open>\<pi> 0 = 0\<close> fix_out lessThan_iff less_one id_def not_less)
next
  show "id permutes {..<1}" by (rule permutes_id)
qed

lemma tropm_det_1x1:
  "tropm_det 1 A = A 0 0"
proof -
  have "tropm_det 1 A
        = \<Sum> \<pi> \<in> {id}. perm_weightm 1 A \<pi>"
    unfolding tropm_det_def
    by (simp add: permutes_lessThan_1)
  also have "\<dots> = perm_weightm 1 A id"
    by simp
  also have "\<dots> = A 0 0"
    unfolding perm_weightm_def by simp
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>5.2  2\<times>2 case\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Prove @{text "Fun.swap 0 1 id"} is a permutation of @{text "{..<2}"}
  directly from @{text permutes_def}.
\<close>

lemma swap_0_1_permutes_lessThan_2:
  "Fun.swap 0 1 id permutes {..<2}"
  unfolding permutes_def
proof (intro conjI allI)
  fix x :: nat
  show "x \<notin> {..<2} \<longrightarrow> Fun.swap 0 1 id x = x"
    by (auto simp: Fun.swap_def)
next
  fix y :: nat
  show "\<exists>!x. Fun.swap 0 1 id x = y"
    by (intro ex1I[of _ "Fun.swap 0 1 id y"])
       (auto simp: Fun.swap_def)
qed

lemma permutes_lessThan_2:
  "{\<pi> :: nat \<Rightarrow> nat. \<pi> permutes {..<2}} = {id, Fun.swap 0 1 id}"
proof (safe)
  fix \<pi> assume h: "\<pi> permutes {..<2}"
  have fix_out: "\<forall>x. x \<notin> {..<2} \<longrightarrow> \<pi> x = x"
    using h unfolding permutes_def by blast
  have bij: "bij \<pi>" using permutes_bij[OF h] .
  have h0: "\<pi> 0 \<in> {..<2}"
    by (metis h permutes_in_image lessThan_iff zero_less_numeral)
  have h1: "\<pi> 1 \<in> {..<2}"
    by (metis h permutes_in_image lessThan_iff one_less_numeral_iff semiring_norm(77))
  have p0: "\<pi> 0 = 0 \<or> \<pi> 0 = 1" using h0 by auto
  show "\<pi> = id \<or> \<pi> = Fun.swap 0 1 id"
  proof (cases "\<pi> 0 = 0")
    case True
    have "\<pi> 1 = 1"
    proof -
      have "\<pi> 1 \<noteq> 0"
      proof
        assume "\<pi> 1 = 0"
        with True have "\<pi> 0 = \<pi> 1" by simp
        with bij have "(0 :: nat) = 1" by (auto simp: bij_def inj_def)
        thus False by simp
      qed
      with h1 show "\<pi> 1 = 1" by auto
    qed
    left
    show "\<pi> = id"
      by (rule ext)
         (metis True \<open>\<pi> 1 = 1\<close> fix_out lessThan_iff numeral_2_eq_2
                less_2_cases id_def)
  next
    case False
    with p0 have pi0: "\<pi> 0 = 1" by simp
    have "\<pi> 1 = 0"
    proof -
      have "\<pi> 1 \<noteq> 1"
      proof
        assume "\<pi> 1 = 1"
        with pi0 have "\<pi> 0 = \<pi> 1" by simp
        with bij have "(0 :: nat) = 1" by (auto simp: bij_def inj_def)
        thus False by simp
      qed
      with h1 show "\<pi> 1 = 0" by auto
    qed
    right
    show "\<pi> = Fun.swap 0 1 id"
      by (rule ext)
         (metis pi0 \<open>\<pi> 1 = 0\<close> fix_out lessThan_iff numeral_2_eq_2
                less_2_cases Fun.swap_def id_def)
  qed
next
  show "id permutes {..<2}" by (rule permutes_id)
next
  show "Fun.swap 0 1 id permutes {..<2}"
    by (rule swap_0_1_permutes_lessThan_2)
qed

lemma tropm_det_2x2:
  "tropm_det 2 A = (A 0 0 * A 1 1) + (A 0 1 * A 1 0)"
proof -
  have neq: "(id :: nat \<Rightarrow> nat) \<noteq> Fun.swap 0 1 id"
    by (simp add: Fun.swap_def fun_eq_iff)
  have "tropm_det 2 A
        = \<Sum> \<pi> \<in> {id, Fun.swap 0 1 id}. perm_weightm 2 A \<pi>"
    unfolding tropm_det_def
    by (simp add: permutes_lessThan_2)
  also have "\<dots> = perm_weightm 2 A id + perm_weightm 2 A (Fun.swap 0 1 id)"
    by (simp add: sum.insert[of "{Fun.swap 0 1 id}" id] neq)
  also have "perm_weightm 2 A id = A 0 0 * A 1 1"
    unfolding perm_weightm_def by simp
  also have "perm_weightm 2 A (Fun.swap 0 1 id) = A 0 1 * A 1 0"
    unfolding perm_weightm_def by (simp add: Fun.swap_def)
  finally show ?thesis .
qed

(* ================================================================== *)
section \<open>6  Optimal Assignment Theorem\<close>
(* ================================================================== *)

text \<open>
  The tropical determinant is the minimum-cost perfect matching:
  \<^item> It is \<open>\<le>\<close> every permutation weight (@{text tropm_det_le_perm}).
  \<^item> It equals at least one permutation weight (@{text tropm_det_mem}).

  Together these give the characteristic property of the minimum.

  This is the formal backing for the @{text ProofOptimalAssignment} VCL
  clause: checking \<open>tropm_det n A \<le> bound\<close> is equivalent to asking whether
  there exists an assignment (permutation) of cost within the bound.
\<close>

theorem optimal_assignment:
  assumes "0 < n"
  shows "\<exists> \<pi>. \<pi> permutes {..<n} \<and>
               tropm_det n A = perm_weightm n A \<pi> \<and>
               (\<forall> \<pi>'. \<pi>' permutes {..<n} \<longrightarrow> tropm_det n A \<le> perm_weightm n A \<pi>')"
proof -
  from tropm_det_mem[OF assms]
  obtain \<pi>\<^sub>0 where
    hperm : "\<pi>\<^sub>0 \<in> {\<pi>. \<pi> permutes {..<n}}"
    and heq : "perm_weightm n A \<pi>\<^sub>0 = tropm_det n A"
    by (auto simp: image_iff)
  show ?thesis
  proof (intro exI[of _ \<pi>\<^sub>0] conjI allI impI)
    show "\<pi>\<^sub>0 permutes {..<n}" using hperm by simp
    show "tropm_det n A = perm_weightm n A \<pi>\<^sub>0" using heq by simp
    fix \<pi>' assume "\<pi>' permutes {..<n}"
    thus "tropm_det n A \<le> perm_weightm n A \<pi>'"
      by (rule tropm_det_le_perm)
  qed
qed

text \<open>
  Corollary: @{text ProofOptimalAssignment} bound semantics.
  The assigned cost is within bound @{text B} if and only if the
  optimal assignment (= tropical determinant) is within @{text B}.
\<close>

corollary optimal_assignment_bound:
  assumes "0 < n"
  shows "(\<exists> \<pi>. \<pi> permutes {..<n} \<and> perm_weightm n A \<pi> \<le> B)
       \<longleftrightarrow> tropm_det n A \<le> B"
proof
  assume "\<exists> \<pi>. \<pi> permutes {..<n} \<and> perm_weightm n A \<pi> \<le> B"
  then obtain \<pi> where h\<pi>: "\<pi> permutes {..<n}" "perm_weightm n A \<pi> \<le> B" by blast
  have "tropm_det n A \<le> perm_weightm n A \<pi>"
    by (rule tropm_det_le_perm[OF h\<pi>(1)])
  thus "tropm_det n A \<le> B" using h\<pi>(2) by (rule order_trans)
next
  assume h: "tropm_det n A \<le> B"
  from optimal_assignment[OF assms]
  obtain \<pi> where
    "\<pi> permutes {..<n}" "tropm_det n A = perm_weightm n A \<pi>" by blast
  thus "\<exists> \<pi>. \<pi> permutes {..<n} \<and> perm_weightm n A \<pi> \<le> B"
    using h by (intro exI[of _ \<pi>]) auto
qed

end
