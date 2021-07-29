(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau sequences.
Require Import derive.

(******************************************************************************)
(*                Definitions and lemmas about exponential                    *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def  Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section fact_facts.

Local Open Scope nat_scope.

Lemma leq_fact n : n <= n`!.
Proof.
by case: n => // n;  rewrite dvdn_leq ?fact_gt0 // dvdn_fact ?andTb.
Qed.

Lemma prod_rev n m :
  \prod_(0 <= k < n - m) (n - k) = \prod_(m.+1 <= k < n.+1) k.
Proof.
rewrite [in RHS]big_nat_rev /= -{1}(add0n m.+1) big_addn subSS.
by apply eq_bigr => i _; rewrite addnS subSS addnC subnDr.
Qed.

Lemma fact_split n m : m <= n -> n`! = \prod_(0 <= k < n - m) (n - k) * m`!.
Proof.
move=> ?; rewrite [in RHS]fact_prod mulnC prod_rev -big_cat [in RHS]/index_iota.
rewrite subn1 -iota_add subSS addnBCA // subnn addn0 [in LHS]fact_prod.
by rewrite [in RHS](_ : n = n.+1 - 1) // subn1.
Qed.

End fact_facts.

Section exponential_series.

Variable R : realType.
Implicit Types x : R.

Import Order.TTheory.
Import Num.Theory.
Import GRing.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition exp_coeff x := [sequence x ^+ n / n`!%:R]_n.

Local Notation exp := exp_coeff.

Lemma exp_coeff_ge0 x n : 0 <= x -> 0 <= exp x n.
Proof. by move=> x0; rewrite /exp divr_ge0 // ?exprn_ge0 // ler0n. Qed.

Lemma series_exp_coeff0 n : series (exp 0) n.+1 = 1.
Proof.
rewrite /series /= big_nat_recl //= /exp /= expr0n divr1 big1 ?addr0 // => i _.
by rewrite expr0n mul0r.
Qed.

Section exponential_series_cvg.

Variable x : R.
Hypothesis x0 : 0 < x.

Let S0 N n := (N ^ N)%:R * \sum_(N.+1 <= i < n) (x / N%:R) ^+ i.

Let is_cvg_S0 N : x < N%:R -> cvg (S0 N).
Proof.
move=> xN; apply: is_cvgZr; rewrite is_cvg_series_restrict exprn_geometric.
apply/is_cvg_geometric_series; rewrite normrM normfV.
by rewrite ltr_pdivr_mulr ?mul1r !ger0_norm // 1?ltW // (lt_trans x0).
Qed.

Let S0_ge0 N n : 0 <= S0 N n.
Proof.
rewrite mulr_ge0 // ?ler0n //; apply sumr_ge0 => i _.
by rewrite exprn_ge0 // divr_ge0 // ?ler0n // ltW.
Qed.

Let S0_sup N n : x < N%:R -> S0 N n <= sup [set of S0 N].
Proof.
move=> xN; apply/sup_upper_bound; [split; [by exists (S0 N n), n|]|by exists n].
rewrite (_ : [set of _] = [set `|S0 N n0| | n0 in setT]).
  by apply: cvg_has_ub (is_cvg_S0 xN).
by rewrite predeqE=> y; split=> -[z _ <-]; exists z; rewrite ?ger0_norm ?S0_ge0.
Qed.

Let S1 N n := \sum_(N.+1 <= i < n) exp x i.

Lemma incr_S1 N : nondecreasing_seq (S1 N).
Proof.
apply/nondecreasing_seqP => n; rewrite /S1.
have [nN|Nn] := leqP n N; first by rewrite !big_geq // (leq_trans nN).
by rewrite big_nat_recr//= ler_addl exp_coeff_ge0 // ltW.
Qed.

Let S1_sup N n : x < N%:R -> S1 N n <= sup [set of S0 N].
Proof.
move=> xN; rewrite (le_trans _ (S0_sup n xN)) // /S0 big_distrr /=.
have N_gt0 := lt_trans x0 xN.
apply ler_sum => i _.
have [Ni|iN] := ltnP N i; last first.
  rewrite expr_div_n mulrCA ler_pmul2l ?exprn_gt0 // (@le_trans _ _ 1) //.
    by rewrite invf_le1 ?ler1n ?ltr0n // fact_gt0.
  rewrite natrX -expfB_cond ?(negPf (lt0r_neq0 N_gt0)) //.
  by rewrite exprn_ege1 // ler1n; case: (N) xN x0; case: ltrgt0P.
rewrite /exp expr_div_n /= (fact_split Ni) mulrCA.
rewrite ler_pmul2l ?exprn_gt0 // natrX -invf_div -expfB //.
rewrite lef_pinv ?qualifE; last 2 first.
- rewrite ltr0n muln_gt0 fact_gt0 andbT.
  rewrite big_mkord prodn_gt0  // => j.
  by rewrite subn_gt0 (leq_trans (ltn_ord _) (leq_subr _ _)).
- by rewrite exprn_gt0.
rewrite prod_rev -natrX ler_nat -prod_nat_const_nat big_add1 /= big_ltn //.
rewrite mulnC leq_mul //; last by apply: leq_trans (leq_fact _).
rewrite -(subnK Ni); elim: (_ - _)%N => [|k IH]; first by rewrite !big_geq.
rewrite !addSn !big_nat_recr //= ?leq_mul ?leq_addl //.
by rewrite -addSn -addSnnS leq_addl.
Qed.

Lemma is_cvg_series_exp_coeff_pos : cvg (series (exp x)).
Proof.
rewrite /series; near \oo => N; have xN : x < N%:R; last first.
  rewrite -(@is_cvg_series_restrict N.+1).
  exact: (nondecreasing_is_cvg (incr_S1 N) (fun n => S1_sup n xN)).
near: N; exists (absz (floor x)).+1 => // m; rewrite /mkset -(@ler_nat R).
move/lt_le_trans => -> //; rewrite (lt_le_trans (lt_succ_Rfloor x)) // -addn1.
rewrite natrD (_ : 1%:R = 1%R) // ler_add2r RfloorE -(@gez0_abs (floor x)) //.
by rewrite floor_ge0// ltW.
Grab Existential Variables. all: end_near. Qed.

End exponential_series_cvg.

Lemma normed_series_exp_coeff x : [normed series (exp x)] = series (exp `|x|).
Proof.
rewrite funeqE => n /=; apply: eq_bigr => k _.
by rewrite /exp normrM normfV normrX [`|_%:R|]@ger0_norm.
Qed.

Lemma is_cvg_series_exp_coeff x : cvg (series (exp x)).
Proof.
have [/eqP ->|x0] := boolP (x == 0).
  apply/cvg_ex; exists 1; apply/cvg_distP => // => _/posnumP[e].
  rewrite near_map; near=> n; have [m ->] : exists m, n = m.+1.
    by exists n.-1; rewrite prednK //; near: n; exists 1%N.
  by rewrite series_exp_coeff0 subrr normr0.
apply: normed_cvg; rewrite normed_series_exp_coeff.
by apply: is_cvg_series_exp_coeff_pos; rewrite normr_gt0.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_exp_coeff x : exp x --> (0 : R).
Proof. exact: (cvg_series_cvg_0 (@is_cvg_series_exp_coeff x)). Qed.

End exponential_series.

(******************************************************************************)
(*  Some addition                                                             *)
(******************************************************************************)

Section cvg_composition.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvg_trans f g a : (f - g) @ F --> (0 : V) -> g @ F --> a -> f @ F --> a.
Proof.
by move=> Cfg Cg; have := cvgD Cfg Cg; rewrite subrK add0r; apply.
Qed.

Lemma cvg_zero f a :
  (f - ((fun _ => a) : _ -> _)) @ F --> (0 : V) -> f @ F --> a.
Proof. by move=> Cfa; apply: cvg_trans Cfa (cvg_cst _). Qed.

End cvg_composition.

Section Cvg.

Variable R : realType.

Lemma cvg_series_bounded (f : R^nat) :
  cvg (series f) ->  exists2 K, 0 < K & (forall i, `|f i| < K).
Proof.
(* There should be something simpler *)
move=> Cf.
have F1 := cvg_series_cvg_0 Cf.
have F2 : bounded_near id [filter of f] by apply: cvg_bounded F1.
have [K1 K1_gt0 KF]:= ex_strict_bound_gt0 F2.
case: KF => x _ Hx.
pose K2 := \sum_(i < x) (1 + `|f i|).
have K2_ge0 : 0 <= K2 by apply: sumr_ge0 => *; apply: addr_ge0.
have K1LK1DK2 : K1 <= K1 + K2 by rewrite -{1}[K1]addr0 ler_add2l.
have K2LK1DK2 : K2 <= K1 + K2 by rewrite -{1}[K2]add0r ler_add2r ltW.
exists (K1 + K2) => [|i]; first by apply: lt_le_trans K1_gt0 _.
have [iLx|xLi] := leqP x i; first by apply: lt_le_trans (Hx i iLx) _.
apply: lt_le_trans K2LK1DK2.
rewrite /K2 (bigD1 (Ordinal xLi)) //=.
rewrite -subr_gt0 addrC !addrA [- _ + _]addrC subrK.
apply: lt_le_trans (_ : 1 <= _) => //.
rewrite -subr_ge0 [1 + _]addrC addrK //.
by apply: sumr_ge0 => *; apply: addr_ge0.
Qed.

Lemma cvg_ext (f g : R^nat) (x : R) : f = g -> (f --> x) = (g --> x).
Proof. by move->. Qed. 

Lemma cvgS (f : R^nat) (x : R) : (f \o S --> x) = (f --> x).
Proof.
have <- /= := @cvg_shiftn 1 _ f x.
by apply/cvg_ext/funext => i; rewrite addn1.
Qed.

Lemma is_cvg_seriesN (f : R^nat) : cvg (series f) -> cvg (series (-f)).
Proof.
move=> Cf.
rewrite /series /= (funext (fun n => sumrN (index_iota 0 n) _ _)).
by apply: is_cvgN => //; apply: is_cvg_cst.
Qed.

Lemma lim_seriesN (f : R^nat) : 
  cvg (series f) -> lim (series (-f)) = - lim (series f).
Proof.
move=> Cf.
rewrite /series /= (funext (fun n => sumrN (index_iota 0 n) _ _)).
by rewrite limN.
Qed.

Lemma is_cvg_seriesZr (f : R^nat) k : cvg (series f) -> cvg (series (k *: f)).
Proof.
move=> Cf.
rewrite /series /= -(funext (fun n => scaler_sumr k (index_iota 0 n) _ _)).
by apply: is_cvgZr => //; apply: is_cvg_cst.
Qed.

Lemma lim_seriesZr (f : R^nat) k : 
  cvg (series f) -> lim (series (k *: f)) = k *: lim (series f).
Proof.
move=> Cf.
rewrite /series /= -(funext (fun n => scaler_sumr k (index_iota 0 n) _ _)).
by rewrite limZr.
Qed.

Lemma is_cvg_seriesD (f g : R^nat) :
  cvg (series f) -> cvg (series g) -> cvg (series (f + g)).
Proof.
move=> Cf Cg.
rewrite /series /= (funext (fun n => big_split _ (index_iota 0 n) _ _ _)) /=.
by apply: is_cvgD.
Qed.

Lemma lim_seriesD (f g : R^nat) : 
  cvg (series f) -> cvg (series g) -> 
  lim (series (f + g)) = lim (series f) + lim (series g).
Proof.
move=> Cf Cg.
rewrite /series /= (funext (fun n => big_split _ (index_iota 0 n) _ _ _)) /=.
by apply: limD.
Qed.

Lemma is_cvg_seriesB (f g : R^nat) :
  cvg (series f) -> cvg (series g) -> cvg (series (f - g)).
Proof.
by move=> Cf Cg; apply: is_cvg_seriesD => //; apply: is_cvg_seriesN.
Qed.

Lemma lim_seriesB (f g : R^nat) : 
  cvg (series f) -> cvg (series g) -> 
  lim (series (f - g)) = lim (series f) - lim (series g).
Proof.
move=> Cf Cg; rewrite lim_seriesD //; last by apply: is_cvg_seriesN.
by rewrite lim_seriesN.
Qed.

Lemma lim_series_norm (f : R^nat) :
  cvg [normed series f] -> `|lim (series f)| <= lim [normed series f].
Proof.
move=> Cnf.
have Cf : cvg (series f) by apply: normed_cvg.
rewrite -lim_norm //.
apply: ler_lim => [|//|]; first by apply: is_cvg_norm.
near=> x.
by rewrite /series /= /series /= ler_norm_sum.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_series_le (f g : (R) ^nat) : 
  cvg (series f) -> cvg (series g) -> (forall n : nat, f n <= g n) -> 
  lim (series f) <= lim (series g).
Proof.
move=> Cf Cg fLg.
apply ler_lim => [//|//|].
near=> x.
by rewrite /series /= ler_sum.
Grab Existential Variables. all: end_near. Qed.

End Cvg.

Section exp.

Variable R : realType.

Definition exp (x : R) : R := lim (series (exp_coeff x)).

Lemma exp0 : exp 0 = 1.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Grab Existential Variables. all: end_near. 
Qed.

Lemma exp_ge x : 0 <= x -> 1 + x <= exp x.
Proof.
 move=> xP; rewrite /exp.
pose f (x : R) i := (i == 0%nat)%:R + x *+ (i == 1%nat).
have F n : (1 < n)%nat -> \sum_(0 <= i < n) (f x i) = 1 + x.
  move=> /subnK<-.
  by rewrite addn2 !big_nat_recl //= /f /= mulr1n !mulr0n big1 ?add0r ?addr0.
have -> : 1 + x = lim (series (f x)).
  by apply/sym_equal/lim_near_cst => //; near=> n; apply: F; near: n.
apply: ler_lim; first by apply: is_cvg_near_cst; near=> n; apply: F; near: n.
  exact: is_cvg_series_exp_coeff.
by near=> n; apply: ler_sum => [] [|[|i]] _;
  rewrite /f /exp_coeff /= !(mulr0n, mulr1n, expr0, expr1, divr1, addr0, add0r)
          // exp_coeff_ge0.
Grab Existential Variables. all: end_near. 
Qed.

Lemma exp_gt_1 x : 0 < x  -> 1 < exp x.
Proof.
move=> xP.
apply: lt_le_trans (exp_ge (ltW xP)).
by rewrite -subr_gt0 addrAC subrr add0r.
Qed.

Fact powdiff n (x y : R) : 
  \sum_(0 <= i < n.+1) x ^+ i  * y ^+ (n.+1 - i) =   
  y * \sum_(0 <= i < n.+1) x ^+ i  * y ^+ (n - i).
Proof.
rewrite !big_mkord mulr_sumr; apply: eq_bigr => i _.
by rewrite mulrCA -exprS subSn // -ltnS.
Qed.

Lemma powdiffE n (x y : R) : 
   x ^+ n.+1 - y ^+ n.+1 = (x - y) * \sum_(0 <= i < n.+1) x ^+ i * y ^+ (n - i).
Proof.
rewrite big_nat_rev /= subrXX /= big_mkord //.
by congr (_ * _); apply: eq_bigr => i _; rewrite subKn // -ltnS.
Qed.

Fact pow_ser_inside_a f (x z : R) :
  cvg (series (fun i => f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => `|f i| * z ^+ i)).
Proof.
move=> Cx zLx.
have [K K_gt0 KP] := cvg_series_bounded Cx.
have F1 := cvg_series_cvg_0 Cx.
have F2 n : 0 <= K * `|z ^+ n| / `|x ^+ n|.
  by rewrite !mulr_ge0 ?invr_ge0 // ltW.
apply: normed_cvg.
apply: series_le_cvg F2 _ _ => [//=| /= n|].
  rewrite (_ : `|_ * _| = `|f n * x ^+ n| * `|z ^+ n| / `|x ^+ n|); last first.
    rewrite !normrM normr_id mulrAC mulfK // normr_eq0 expf_eq0 andbC.
    by case: ltrgt0P zLx; rewrite //= normr_lt0.
  do! (apply: ler_pmul || apply: mulr_ge0 || rewrite invr_ge0) => //.
  by apply: ltW.
have F : `|z / x| < 1.
  by rewrite normrM normfV ltr_pdivr_mulr ?mul1r // (le_lt_trans _ zLx).
rewrite (_ : (fun _ => _) = geometric K `|z / x|).
apply: is_cvg_geometric_series; first by rewrite normr_id.
apply/funext => i /=.
by rewrite normrM exprMn mulrA normfV !normrX exprVn.
Qed.

Fact pow_ser_inside f (x z : R) :
  cvg (series (fun i => f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => f i * z ^+ i)).
Proof.
move=> Cx zLx.
apply: normed_cvg; rewrite /normed_series_of /=.
rewrite (_ : (fun _ => _) = (fun i : nat => `|f i| * `|z| ^+ i)); last first.
  by apply/funext => i; rewrite normrM normrX.
by apply: pow_ser_inside_a Cx _; rewrite normr_id.
Qed.

Definition diffs (f : nat -> R) i := i.+1%:R * f i.+1.

Lemma diffsN (f : nat -> R) :  diffs (- f) = -(diffs f).
Proof. by apply/funext => i; rewrite /diffs /= -mulrN. Qed.

Lemma diffs_sumE n f x :
 \sum_(0 <= i < n) diffs f i * x ^+ i =
 (\sum_(0 <= i < n) i%:R * f i * x ^+ i.-1) + n%:R * f n * x ^+ n.-1.
Proof.
case: n => [|n]; first by rewrite !big_nil !mul0r add0r.
under eq_bigr do unfold diffs.
by rewrite big_nat_recr //= big_nat_recl //= !mul0r add0r.
Qed.

Lemma cvg_ext1 : forall (R : realType) (f g : (R) ^nat),
  f = g -> (f --> lim f) = (g --> lim g).
Proof. by move=> R1 f1 g1 ->. Qed.

Lemma diffs_equiv f x :
  cvg (series (fun i => diffs f i * x ^+ i)) ->
  series (fun i => i%:R * f i * x ^+ i.-1) -->
  lim (series (fun i => diffs f i * x ^+ i)).
Proof.
move=> Cx.
rewrite -[lim _]subr0.
rewrite {2}/series /=.
have F n : \sum_(0 <= i < n) i%:R * f i * x ^+ i.-1 =
           (\sum_(0 <= i < n) diffs f i * x ^+ i) - n%:R * f n * x ^+ n.-1.
    by rewrite diffs_sumE addrK. 
rewrite (cvg_ext _ (funext F)).
apply: cvgB => //; rewrite -cvgS.
by apply: cvg_series_cvg_0.
Qed.

Lemma cvg_diffs_equiv f x :
  cvg (series (fun i => diffs f i * x ^+ i)) ->
  cvg (series (fun i => i%:R * f i * x ^+ i.-1)).
Proof.
move=> Cx.
have F1 := diffs_equiv Cx.
by rewrite (cvg_lim _ (F1)).
Qed.

Lemma termdiff_P1 m (z h : R) :
  \sum_(0 <= i < m) ((z + h) ^+ (m - i) * z ^+ i - z ^+ m) =
  \sum_(0 <= i < m) z ^+ i * ((z + h) ^+ (m - i) - z ^+ (m - i)).
Proof.
rewrite !big_mkord; apply: eq_bigr => i _.
by rewrite mulrDr mulrN -exprD mulrC addnC subnK // ltnW.
Qed.

Lemma termdiff_P2 n (z h : R) :
  h != 0 ->
  ((z + h) ^+ n - (z ^+ n)) / h - n%:R * z ^+ n.-1 =
  h * \sum_(0 <= i < n.-1) z ^+ i *
      \sum_(0 <= j < n.-1 - i) (z + h) ^+ j * z ^+ (n.-2 - i - j).
Proof.
move=> hNZ; apply: (mulfI hNZ).
rewrite mulrBr mulrC divfK //.
case: n => [|n].
  by rewrite !expr0 !(mul0r, mulr0, subr0, subrr, big_geq).
rewrite subrXX /= {1}[z + _]addrC addrK -mulrBr; congr (_ * _).
rewrite -(big_mkord xpredT (fun i : nat => (z + h) ^+ (n - i) * z ^+ i)).
rewrite big_nat_recr //= subnn expr0 -addrA -mulrBl.
rewrite  -add1n natrD opprD addrA subrr sub0r mulNr.
rewrite mulr_natl -{4}(subn0 n) -sumr_const_nat -sumrB.
rewrite termdiff_P1 mulr_sumr !big_mkord; apply: eq_bigr => i _.
rewrite mulrCA; congr (_ * _).
rewrite subrXX {1}[z + _]addrC addrK big_nat_rev /= big_mkord.
congr (_ * _); apply: eq_bigr => k _.
by rewrite -!predn_sub subKn // -subnS.
Qed.

Lemma termdiff_P3 (z h : R) n K :
 h != 0 -> `|z| <= K -> `|z + h| <= K ->
    `|((z + h) ^+ n - z ^+ n) / h - n%:R * z ^+ n.-1|
        <= n%:R * n.-1%:R * K ^+ n.-2 * `|h|.
Proof.
move=> hNZ zLK zhLk.
have KP : 0 <= K by apply: le_trans zLK.
rewrite termdiff_P2 // normrM mulrC.
rewrite ler_pmul2r ?normr_gt0 //.
apply: le_trans (ler_norm_sum _ _ _) _.
rewrite -mulrA mulrC -mulrA.
rewrite -{4}[n.-1]subn0 mulr_natl -sumr_const_nat.
rewrite !big_mkord; apply: ler_sum => i _.
rewrite normrM /=.
case: n i => //= [[]//| n i].
pose d := (n.-1 - i)%nat.
rewrite -[(n - i)%nat]prednK ?subn_gt0 // predn_sub -/d.
rewrite -(subnK (_ : i <= n.-1)%nat) -/d; last first.
  by rewrite -ltnS prednK // (leq_trans _ (ltn_ord i)).
rewrite addnC exprD mulrAC -mulrA.
apply: ler_pmul => //.
  by rewrite normrX ler_expn2r ?qualifE // (le_trans _ zLK).
apply: le_trans (_ : d.+1%:R * K ^+ d <= _); last first.
  rewrite ler_wpmul2r //; first by rewrite exprn_ge0 // (le_trans _ zLK).
  rewrite ler_nat ltnS (leq_trans (leq_subr _ _)) // -ltnS prednK //.
  by rewrite (leq_ltn_trans _ (ltn_ord i)).
apply: le_trans (ler_norm_sum _ _ _) _.
rewrite -{2}[d.+1]subn0 mulr_natl -sumr_const_nat.
rewrite !big_mkord; apply: ler_sum => j _.
rewrite -{4}(subnK (_ : j <= d)%nat) -1?ltnS // addnC exprD normrM.
by apply: ler_pmul; rewrite // normrX ler_expn2r ?qualifE.
Qed.

Lemma termdiff_P4 (f : R -> R) K k :
  0 < k -> (forall h, 0 < `|h| < k -> `|f h| <= K * `|h|) ->
    f x @[x --> nbhs' (0 : R)] --> (0 : R).
Proof.
(* There should be a shorter proof *)
move=> k_gt0 H; apply/cvg_distP => /= eps eps_gt0; rewrite !near_simpl.
pose k2 : R := k / 2.
have k2_gt0 : 0 < k2 by rewrite divr_gt0.
have k2Lk : k2 < k.
  by rewrite ltr_pdivr_mulr // mulr2n mulrDr mulr1 -subr_gt0 addrK.
have : 0 <= K.
  rewrite -(pmulr_rge0 _ k2_gt0) mulrC -(gtr0_norm k2_gt0).
  apply: le_trans (H _ _) => //.
  by rewrite ger0_norm  ?k2_gt0 // ltW.
rewrite le_eqVlt => /orP[/eqP K_eq0| K_gt0].
  pose k3 := if k2 < eps then k2 else eps.
  have k3_gt0 : 0 < k3 by rewrite /k3; case: (k2 < _).
  have k3Lk : k3 < k.
    by rewrite /k3; case: (ltrP k2) => // /le_lt_trans ->. 
  exists k3 => //= t /=; rewrite !sub0r !normrN.
  move=> H1 Ht.
  apply: le_lt_trans (H _ _) _.
    apply/andP; split; first by rewrite normr_gt0.
    by apply: lt_trans H1 _.
  by rewrite -K_eq0 mul0r.
pose k3 := if k2 < eps / K then k2 else eps / K.
have k3_gt0 : 0 < k3.
  by rewrite /k3; case: (k2 < _); rewrite // divr_gt0.
have k3Lk : k3 < k.
  by rewrite /k3; case: (ltrP k2) => // /le_lt_trans ->.
have k3Le : K * k3 <= eps.
  rewrite -[eps](divfK (_ : K != 0)).
    rewrite mulrC ler_pmul2r //.
    rewrite /k3; case: (ltrP k2) => //.
    by move/ltW.
  by case: (ltrgt0P K) K_gt0.
exists k3 => //= t /=; rewrite !sub0r !normrN.
move=> H1 H2.
have : `|f t| <= K * `|t|.
  apply/H/andP; split.
    by rewrite normr_gt0.
  by apply: lt_trans H1 _.
  move=> /le_lt_trans ->//.
  apply: lt_le_trans k3Le.
  by rewrite ltr_pmul2l //.
Qed.

Lemma termdiff_P (f : nat -> R) (g : R -> nat -> R) k :
  0 < k -> cvg (series f) ->
    (forall h : R, 0 < `|h| < k -> forall n, `|g h n| <= f n * `|h|) ->
     lim (series (g x)) @[x --> nbhs' (0 : R)] --> (0 : R).
Proof.
move=> k_gt0 Cf Hg.
apply: (@termdiff_P4 _ (lim (series f)) k) => // h hLk; rewrite mulrC.
have Ckf := @is_cvg_seriesZr _ _ `|h| Cf.
have Lkf := lim_seriesZr `|h| Cf.
have Cng : cvg [normed series (g h)].
  apply: series_le_cvg (Hg _ hLk) _  => //.
    by move=> h1; apply: le_trans (Hg _ hLk _).
  by rewrite (funext (fun n => (@mulrC R _ _))).
apply: le_trans (_ : lim [normed series (g h)] <= _).
  by apply: lim_series_norm.
rewrite -[_ * _]lim_seriesZr //.
apply: lim_series_le => //=.
move=> n; rewrite [X in _ <= X]mulrC. 
by apply: Hg.
Qed.

Lemma termdiff (c : R^nat) K x :
  cvg (series (fun n => c n * K ^+ n)) ->
  cvg (series (fun n => diffs c n * K ^+ n)) ->
  cvg (series (fun n => diffs (diffs c) n * K ^+ n)) ->
  `|x| < `|K| ->
  (fun x => lim (series (fun n => c(n) * x ^+ n)))^`() x =
    lim (series (fun n => diffs c n * x ^+ n)).
Proof.
move=> Ck CdK CddK xLK.
set s := (fun n : nat => _).
apply: cvg_lim => //.
pose sx := fun n : nat => c n * x ^+ n.
have Csx : cvg (series sx) by apply: pow_ser_inside Ck _.
pose shx h := fun n : nat => c n * (h + x) ^+ n.
suff Cc : 
      lim (h^-1 *: (series (shx h - sx))) @[h --> nbhs' 0] --> lim (series s).
  apply: cvg_trans Cc.
  apply/cvg_distP => eps eps_gt0 /=.
  rewrite !near_simpl /=.
  near=> h; rewrite sub0r normrN /=.
  apply: le_lt_trans eps_gt0.
  rewrite normr_le0 subr_eq0; apply/eqP.
  rewrite -/sx -/(shx _).
  have Cshx : cvg (series (shx h)).
    apply: pow_ser_inside Ck _.
    apply: le_lt_trans (ler_norm_add _ _) _.
    rewrite -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    apply: lt_le_trans H _.
    rewrite ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  rewrite limZr; last by apply: is_cvg_seriesB.
  by rewrite lim_seriesB.
apply: cvg_zero => /=.
(* Need cleaning *)
suff Cc : 
  lim (series
       (fun n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1)))
   @[h --> nbhs' 0] --> (0 : R).
  apply: cvg_trans Cc.
  apply/cvg_distP => eps eps_gt0 /=.
  rewrite !near_simpl /=.
  near=> h; rewrite sub0r normrN /=.
  apply: le_lt_trans eps_gt0.
  rewrite normr_le0 subr_eq0; apply/eqP.
  set u := (fun n => _); set v := (fun _ => _); set w := (fun n => _).
  rewrite /-%R /+%R /= {}/u {}/v {}/w.
  have Cs : cvg (series s).
    by apply: pow_ser_inside CdK _.
  have Cs1 := cvg_diffs_equiv (Cs).
  have Fs1 := diffs_equiv (Cs).
  set s1 := (fun i => _) in Cs1.
  have Cshx : cvg (series (shx h)).
    apply: pow_ser_inside Ck _.
    apply: le_lt_trans (ler_norm_add _ _) _.
    rewrite -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    apply: lt_le_trans H _.
    rewrite ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  have C1 := is_cvg_seriesB Cshx Csx.
  have Ckf := @is_cvg_seriesZr _ _ h^-1 C1.
  have Cu : (series (h^-1 *: (shx h - sx)) -
             series s1) x0 @[x0 --> \oo] --> 
            lim (series (h^-1 *: (shx h - sx))) -
            lim (series s).
    by apply: cvgB.
  set w := fun n : nat => _.
  have -> : w = h^-1 *: (shx h - sx)  - s1.
    apply: funext => i /=; rewrite /-%R  /+%R /*:%R /=.
    rewrite /w /shx /sx /s1 /= mulrBr; congr (_ - _); last first.
      by rewrite mulrCA !mulrA.
    by rewrite -mulrBr [RHS]mulrCA [_^-1 * _]mulrC.
  have -> : series (h^-1 *: (shx h - sx) - s1) = 
            series (h^-1 *: (shx h - sx)) - (series s1).
    by apply/funext => i; rewrite /series /= sumrB.
  have -> : h^-1 *: series (shx h - sx) =
            series (h^-1 *: (shx h - sx)).
    by apply/funext => i; rewrite /series /= -scaler_sumr.
  by apply/sym_equal/cvg_lim.
pose r := (`|x| + `|K|) / 2.
have xLr : `|x| < r.
  by rewrite ltr_pdivl_mulr // mulr2n mulrDr mulr1 ltr_add2l.
have rLx : r < `|K| .
  by rewrite ltr_pdivr_mulr // mulr2n mulrDr mulr1 ltr_add2r.
have rNZ : r != 0.
  have : 0 < r by apply: le_lt_trans xLr.
  by case: ltrgt0P.
apply: (@termdiff_P
  (fun n => `|c n| * n%:R * (n.-1)%:R * r ^+ n.-2)
  (fun h n => c n * (((h + x) ^+ n - x ^+ n) / h -
                     n%:R * x ^+ n.-1))
  (r - `|x|)) => //.
- by rewrite subr_gt0.
- have : cvg (series (fun n => `|diffs (diffs c) n| * r ^+ n)).
    apply: pow_ser_inside_a CddK _.
    by rewrite ger0_norm // ltW // (le_lt_trans _ xLr).
  have -> : (fun n : nat => `|diffs (diffs c) n| * r ^+ n) = 
            (fun n => diffs (diffs (fun m => `|c m|)) n * r ^+ n).
    apply/funext => i.
    by rewrite /diffs !normrM !mulrA ger0_norm // ger0_norm.
  move=> /cvg_diffs_equiv.
  rewrite /diffs.
  have -> :
         (fun n => n%:R * ((n.+1)%:R * `|c n.+1|) * r ^+ n.-1) =
         (fun n => diffs (fun m => (m.-1)%:R * `|c m| * r^-1) n * r ^+ n).
    apply/funext => n.
    rewrite /diffs /= mulrA.
    case: n => [|n /=]; first by rewrite !(mul0r, mulr0).
    rewrite [_%:R *_]mulrC !mulrA -[RHS]mulrA exprS.
    by rewrite [_^-1 * _]mulrA mulVf ?mul1r.
  move/cvg_diffs_equiv.
  have ->// : (fun i : nat => i%:R * (i.-1%:R * `|c i| / r) * r ^+ i.-1) =
              (fun n : nat => `|c n| * n%:R * n.-1%:R * r ^+ n.-2).
  apply/funext => [] [|[|i]]; rewrite ?(mul0r, mulr0) //=.
  rewrite mulrA -mulrA exprS [_^-1 * _]mulrA mulVf //.
  rewrite mul1r !mulrA; congr (_ * _).
  by rewrite mulrC mulrA.
move=> h H1 n.
rewrite normrM -!mulrA ler_wpmul2l //.
rewrite [h + _]addrC.
apply: le_trans (termdiff_P3 _ _ _ _) _.
- case/andP: H1.
  by case: (ltrgt0P h) => //; rewrite ltxx.
- by apply/ltW/xLr.
- apply: le_trans (ler_norm_add _ _) _.
  rewrite -(subrK `|x| r) addrC ler_add2r ltW //.
  by case/andP: H1.
by rewrite !mulrA.
Grab Existential Variables. all: end_near. Qed.

End exp.
