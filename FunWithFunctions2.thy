(*  
  Title:      Fun with Functions 2
  Author:     Manuel Eberl
*)
theory FunWithFunctions2
imports Transcendental
begin

text {*
  A slightly different introduction rule for the limit of a sequence. This rule allows the 
  lower bound to be real instead of a natural number.
*}
lemma LIMSEQ_I': 
  assumes "\<And>r. 0 < r \<Longrightarrow> \<exists>(n0::real). \<forall>(n::nat)>n0. norm (X n - L) < r"
  shows "X ----> L"
proof (rule LIMSEQ_I)
  fix \<epsilon>::real assume "0 < \<epsilon>"
  from assms[OF this] guess n\<^sub>0 ..
  note n\<^sub>0_props = this
  def n\<^sub>0' \<equiv> "natceiling (n\<^sub>0) + 1"
  hence "n\<^sub>0' > n\<^sub>0" using real_natceiling_ge[of n\<^sub>0] by simp
  with n\<^sub>0_props have "\<forall>n\<ge>n\<^sub>0'. norm (X n - L) < \<epsilon>" by simp
  thus "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. norm (X n - L) < \<epsilon>" ..
qed

text {*
  Two continuous real functions that have the same values on the rationals must be equal.
*}
lemma continuous_completion:
  fixes f :: "real \<Rightarrow> real" and c::real
  assumes cont_f: "\<And>x. isCont f x"
  assumes cont_g: "\<And>x. isCont g x"
  assumes eq_on_rats: "\<And>x. x\<in>\<rat> \<Longrightarrow> f x = g x"
  shows "f = g"
proof
  fix x::real
  def a \<equiv> "\<lambda>n. SOME r. r \<in> \<rat> \<and> x < r \<and> r < x + inverse (Suc n)"

  {
    fix n
    from Rats_dense_in_real[of "x" "x+inverse (Suc n)"] 
      obtain r where "r \<in> \<rat> \<and> x < r \<and> r < x+inverse (Suc n)" (is "?P r")
      by (force simp: field_simps)
    from someI[of ?P r, OF this]
      have "a n \<in> \<rat>" and "x < a n" and "a n < x+inverse (Suc n)" 
      unfolding a_def by simp_all
  } note a_props = this

  have conv: "a ----> x"
  proof (rule LIMSEQ_I')
    fix \<epsilon>::real assume "\<epsilon> > 0"
    def n\<^sub>0 \<equiv> "inverse \<epsilon>"
    have [simp]: "n\<^sub>0 > 0" using `\<epsilon> > 0` unfolding n\<^sub>0_def by simp
    {
      fix n::nat assume "n > n\<^sub>0"
      note n_pos = less_trans[OF `n\<^sub>0 > 0` this]
      have "norm (a n - x) < inverse (Suc n)" using a_props[of n] by simp
      also have "... \<le> inverse n" using n_pos by simp
      also from `n > n\<^sub>0` and `n\<^sub>0 > 0` have "... < \<epsilon>" unfolding n\<^sub>0_def `\<epsilon> > 0` n_pos
        using less_imp_inverse_less by force
      finally have "norm (a n - x) < \<epsilon>" .
    }
    thus "\<exists>n0\<Colon>real. \<forall>n\<Colon>nat. n0 < real n \<longrightarrow> norm (a n - x) < \<epsilon>" by blast
  qed

  from a_props have "(\<lambda>n. f (a n)) = (\<lambda>n. g (a n))" using assms by (intro ext) force
  moreover from isCont_tendsto_compose[OF cont_f conv]
    have "(\<lambda>n. f (a n)) ----> f x" by blast
  moreover from isCont_tendsto_compose[OF cont_g conv] 
    have "(\<lambda>n. g (a n)) ----> g x" by blast
  ultimately show "f x = g x" using LIMSEQ_unique by force
qed

text {*
  A continuous additive function is always linear, i.e. @{term "\<lambda>x. a * x"} for some @{term "a"}.
*}
lemma additive_imp_linear:
  fixes f :: "real \<Rightarrow> real"
  assumes add: "\<And>x y. f (x + y) = f x + f y" and cont: "\<And>x. isCont f x"
  shows "f x = f 1 * x"
proof-
  from add[of 0 0] have f_0: "f 0 = 0" by simp

  have f_neg: "\<And>x. f (-x) = -f x"  proof-
    fix x::real
    show "f(-x) = -f x" using add[of "x" "-x"] by (simp add: f_0)
  qed

  have f_frac: "\<And>(m::nat) (n::nat). n > (0::nat) \<Longrightarrow> f (m/n) = m * f (1/n)"
    by (induct_tac m rule: nat.induct)
       (simp_all add: f_0 real_of_nat_Suc add_divide_distrib add distrib_right)

  have f_inv: "\<And>n::nat. n > (0::nat) \<Longrightarrow> f (1 / n) = 1 / n * f 1"
  proof-
    fix n::nat assume "n > 0"
    with f_frac[OF this, of n] have "n * f (1 / n) = f 1" by simp
    thus "f (1 / n) = 1 / n * f 1" using `n > 0` by (simp add: field_simps) 
  qed

  have f_frac2: "\<And>(m::nat) (n::nat). n > 0 \<Longrightarrow> f (real m / real n) = real m / real n * f 1"
  proof-
    fix n::nat and m::nat assume "n > 0"
    from f_frac[OF this] and f_inv[OF this]
      show "f (m / n) = (m / n) * f 1" by simp
  qed
  
  have f_rat: "\<And>r. r \<in> \<rat> \<Longrightarrow> f r = f 1 * r"
  proof-
    fix r::real assume rat: "r \<in> \<rat>"
    have f_rat_aux: "\<And>r. r \<in> \<rat> \<Longrightarrow> 0 \<le> r \<Longrightarrow> f r = r * f 1"
    proof-
      fix r::real assume "r \<in> \<rat>" and "r \<ge> 0"
      from Rats_abs_nat_div_natE[OF this(1)] and this(2) and abs_of_nonneg
        obtain m::nat and n::nat where "n \<noteq> 0" and "r = m / n" by metis
      with f_frac2[of n m] show "f r = r * f 1" by simp
    qed
    show "f r = f 1 * r" using f_rat_aux[of r] f_rat_aux[of "-r"] rat f_neg
      by (cases "r \<ge> 0") simp_all
  qed

  let ?g = "\<lambda>x. f 1 * x"
  have "\<And>x. isCont ?g x" by auto
  from fun_cong[OF continuous_completion[OF cont this f_rat]]
    show "f x = f 1 * x" .
qed

text {*
  A continuous function for which multiplying the arguments is equivalent to adding the result 
  is always the natural logarithm multiplied with some constant.
*}
lemma mult_to_add_imp_log:
  fixes g :: "real \<Rightarrow> real"
  assumes mult_add: "\<And>x y. x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> g (x * y) = g x + g y"
      and g_cont: "\<And>x. x > 0 \<Longrightarrow> isCont g x"
  assumes "x > 0"
  shows   "g x = g (exp 1) * ln x"
proof-
  def f \<equiv> "g \<circ> exp"
  from isCont_o[OF isCont_exp g_cont] and exp_gt_zero
    have f_cont: "\<And>x. isCont f x" unfolding f_def .

  have f_additive: "\<And>x y. f (x + y) = f x + f y"
    by (simp add: field_simps exp_add mult_add f_def)
  
  from f_additive f_cont have "f (ln x) = f 1 * ln x" using additive_imp_linear by blast
  with `x > 0` show "g x = g (exp 1) * ln x" unfolding f_def o_def by simp
qed

text {*
  A variation of the previous lemma: a continuous function for which multiplying the arguments 
  is equivalent to adding the result is always a logarithm to some non-zero base. 
  (or the constant zero function)
*}
lemma mult_to_add_imp_log':
  fixes g :: "real \<Rightarrow> real"
  assumes mult_add: "\<And>x y. x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> g (x * y) = g x + g y"
      and g_cont: "\<And>x. x > 0 \<Longrightarrow> isCont g x"
  assumes nonzero: "\<exists>x>0. g x \<noteq> 0" 
  assumes "x > 0"
  shows   "g x = log (exp (inverse (g (exp 1)))) x"
proof-
  from nonzero obtain y where "y > 0" and "g y \<noteq> 0" by blast
  moreover with assms have "g y = g (exp 1) * ln y" by (intro mult_to_add_imp_log)
  ultimately have "g (exp 1) \<noteq> 0" by auto

  from assms have g: "g x = g (exp 1) * ln x" by (intro mult_to_add_imp_log)
  also from `g (exp 1) \<noteq> 0` have "g (exp 1) * ln x = log (exp (inverse (g (exp 1)))) x"
    unfolding log_def by (simp add: field_simps ln_div)
  finally show ?thesis .
qed


text {*
  A continuous function for which adding the arguments is equivalent to multiplying the result 
  is always an exponential function to some non-zero base, i.e. 
  @{term "\<lambda>x. a ^ x"} for some @{term "a"}}. (or the constant zero function)
*}
lemma add_to_mult_imp_exp:
  fixes g :: "real \<Rightarrow> real"
  assumes add_mult: "\<And>x y. g (x + y) = g x * g y"
      and g_cont:   "\<And>x. isCont g x"
      and nonzero:  "\<exists>x. g x \<noteq> 0"
  shows "g x = g 1 powr x"
proof-
  have nonzero: "\<And>x. g x \<noteq> 0"
  proof
    fix y :: real assume "g y = 0"
    from nonzero obtain x where "g x \<noteq> 0" ..
    have "x = (x - y) + y" by simp
    also have "g ... = g (x - y) * g y" by (subst add_mult) simp
    also from `g y = 0` have "... = 0" by simp
    finally show False using `g x \<noteq> 0` by contradiction
  qed    

  have pos: "\<And>x. g x > 0"
  proof-
    fix x :: real
    have "x = x / 2 + x / 2" by (simp add: field_simps)
    also have "g ... = g (x / 2) * g (x / 2)" by (rule add_mult)
    also have "... \<ge> 0" by simp
    finally show "g x > 0" using nonzero[of x] by simp
  qed

  def f \<equiv> "ln \<circ> g"
  have f_additive: "\<And>x y. f (x + y) = f x + f y"
    unfolding f_def by (simp add: o_def add_mult pos ln_mult)
  from g_cont nonzero have f_cont: "\<And>x. isCont f x" unfolding f_def
    by (auto intro!: isCont_o isCont_ln)
  
  have "g x = exp (ln (g x))" by (simp add: pos)
  also from additive_imp_linear[OF f_additive f_cont] have "ln (g x) = ln (g 1) * x"
    unfolding f_def o_def .
  also have "exp ... = g 1 powr x" unfolding powr_def by simp
  finally show "g x = g 1 powr x" .
qed
    

text {*
  A continuous multiplicative function is always a power function, i.e. 
  @{term "\<lambda>x. x ^ a"} for some @{term "a"}}. (or the constant zero function)
*}
lemma multiplicative_imp_powr:
  fixes h :: "real \<Rightarrow> real"
  assumes mult: "\<And>x y. x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> h (x * y) = h x * h y" and h_cont: "\<And>x. isCont h x"
  assumes nonzero: "\<exists>x>0. h x \<noteq> 0"
  assumes "x > 0"
  shows   "h x = x powr ln (h (exp 1))"
proof-
  have nonzero: "\<And>x. x > 0 \<Longrightarrow> h x \<noteq> 0"
  proof
    fix y :: real assume "y > 0" "h y = 0"
    from nonzero obtain x where "x > 0" "h x \<noteq> 0" by blast
    from `y > 0` have "x = (x / y) * y" by (simp add: field_simps)
    also from `x > 0` and `y > 0` have "h ... = h (x / y) * h y" by (intro mult) simp
    also from `h y = 0` have "... = 0" by simp
    finally show False using `h x \<noteq> 0` by contradiction
  qed

  have h_pos: "\<And>x. x > 0 \<Longrightarrow> h x > 0"
  proof-
    fix x::real
    assume "x > 0"
    hence "sqrt x * sqrt x = x"
      by (simp add: real_sqrt_mult[symmetric])
    hence "h x = h (sqrt x * sqrt x)" by simp
    also from mult[of "sqrt x" "sqrt x"] and `x > 0` 
      have "... = h (sqrt x) * h (sqrt x)" by simp
    also have "... = h (sqrt x) ^ 2" by (simp add: power2_eq_square)
    also have "... > 0" using nonzero and `x > 0` by simp
    finally show "h x > 0" .
  qed

  def f \<equiv> "ln \<circ> h"
  from h_cont have f_cont: "\<And>x. x > 0 \<Longrightarrow> isCont f x" unfolding f_def 
    by (auto intro!: isCont_o isCont_ln dest: h_pos)
  have f_mult_add: "\<And>x y. x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> f (x * y) = f x + f y"
  proof-
    fix x y :: real
    assume "x > 0" and "y > 0"
    with h_pos show "f (x * y) = f x + f y" unfolding f_def
      by (simp add: field_simps mult ln_mult)
  qed

  from `x > 0` have "h x = exp (ln (h x))" by (simp add: h_pos)
  also from `x > 0` have "ln (h x) = ln (h (exp 1)) * ln x"
    using mult_to_add_imp_log[OF f_mult_add f_cont] unfolding f_def o_def by blast
  hence "exp (ln (h x)) = x powr ln (h (exp 1))" unfolding powr_def by simp
  finally show "h x = x powr ln (h (exp 1))" .
qed
      
end