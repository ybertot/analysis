From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical_sets posnum topology
  normedtype landau sequences boolp reals ereal derive.

Import GRing.Theory Num.Theory Num.ExtraDef.
Import Order.POrderTheory Order.TotalTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section real_inverse_functions.

Variable R : realType.

Let Cf (f : R -> R) a b := {in `[a, b], continuous f}.
Let If (f : R -> R) a b := {in `[a, b] &, injective f}.
Let Mf (f : R -> R) a b := {in `[a, b] &, {mono f : x y / x <= y}}.
Let MTf (f : R -> R) a b :=
  {in `[a, b] &, {mono f : x y / x <= y}} \/
  {in `[a, b] &, {mono f : x y /~ x <= y}}.

Lemma triplet_injective_increasing (f : R -> R) (a c b : R) :
  f a <= f b -> If f a b -> Cf f a b -> a <= c <= b -> f a <= f c <= f b.
Proof.
move=> faLfb fI fC /andP[aLc cLb].
have aLb : a <= b  by apply: le_trans cLb.
have cIab : c \in `[a,b] by rewrite in_itv /= aLc.
have acIab d : d \in `[a,c] -> d \in `[a,b].
  by move=> /itvP dI; rewrite in_itv /= (le_trans _ cLb) // dI.
have cbIab d : d \in `[c,b] -> d \in `[a,b].
  by move=> /itvP dI; rewrite in_itv /= (le_trans aLc) // dI.
case: (ltrgtP (f a) (f c)) => /= [faLfc|fcLfa|faEfc]; last first.
- by rewrite -(fI _  _ _ _ faEfc) // in_itv /= lexx.
- case: (ltrgtP (f b) (f c))=> /= [fbLfc|fcLfb|fbEfc]; last first.
  + by move: fcLfa; rewrite -fbEfc ltNge faLfb.
  + have [d dI]: exists2 d, d \in `[c, b] & f d = f a.
      apply: IVT => //; first by move=> d dIab; apply/fC/cbIab.
      by case: ltrgtP fcLfb => // _ _; rewrite ltW.
    move=> fdEfa; move: fcLfa.
    have : a <= c <= d by rewrite aLc  (itvP dI).
    rewrite (fI _  _ _ _ fdEfa) ?in_itv /= ?lexx ?(itvP dI) //.
      by case: (ltrgtP a) => // ->; rewrite ltxx.
    by rewrite (le_trans aLc) //  (itvP dI).
  by have := lt_trans fbLfc fcLfa; rewrite ltNge faLfb.
case: (ltrgtP (f b) (f c))=> //= fbLfc.
have [d dI]: exists2 d, d \in `[a, c] & f d = f b.
  apply: IVT => //; first by move=> d dIab; apply/fC/acIab.
  by case: ltrgtP faLfc; rewrite // faLfb // ltW.
move=> fdEfb; move: fbLfc.
have : d <= c <= b by rewrite cLb  (itvP dI).
rewrite (fI _  _ _ _ fdEfb) ?in_itv /= ?lexx ?(itvP dI) ?aLb //.
  by case: (ltrgtP b) => //= ->; rewrite ltxx.
by rewrite (le_trans _ cLb) //  (itvP dI).
Qed.

Lemma segment_injective_increasing (f : R -> R) (a b : R) :
  f a <= f b -> If f a b -> Cf f a b -> Mf f a b.
Proof.
move=> faLfb fI fC x y /itvP xI /itvP yI.
have aLb : a <= b by apply: le_trans (_ : x <= b); rewrite xI.
have : x <= y -> f x <= f y.
  move=> xLy.
  have /andP[faLfx fxLfb] : f a <= f x <= f b.
    by apply: triplet_injective_increasing ; rewrite ?xI.
  suff /andP[-> //] : f x <= f y <= f b.
  apply: triplet_injective_increasing
    => [|x1 x2 /itvP x1I /itvP x2I |x1 /itvP x1I|] //.
    - by apply: fI; rewrite in_itv /= (le_trans (_ : a <= x)) !(xI, x1I,
x2I).
    - by apply: fC; rewrite in_itv /= (le_trans (_ : a <= x)) !(xI, x1I).
    by rewrite xLy yI.
have : y <= x -> f y <= f x.
  move=> yLx.
  have /andP[faLfx fxLfb] : f a <= f y <= f b.
    by apply: triplet_injective_increasing; rewrite ?yI.
  suff /andP[-> //] : f y <= f x <= f b.
  apply: triplet_injective_increasing
     => [|x1 x2 /itvP x1I /itvP x2I |x1 /itvP x1I|] //.
  - by apply: fI; rewrite in_itv /= (le_trans (_ : a <= y)) !(yI, x1I, x2I).
  - by apply: fC; rewrite in_itv /= (le_trans (_ : a <= y)) !(yI, x1I).
  by rewrite yLx xI.
have : f x == f y -> x == y.
  by move=> /eqP/fI-> //; rewrite in_itv /= !(xI, yI).
by case: (ltrgtP x y); case: (ltrgtP (f x) (f y)) => // _ _ H1 H2 H3;
     (case: (H1 isT) || case: (H2 isT) || case: (H3 isT)).
Qed.

Lemma segment_injective_monotone (f : R -> R) (a b : R) :
  If f a b -> Cf f a b -> MTf f a b.
Proof.
move=> fI fC.
have [faLfb|fbLfa] : f a <= f b \/ f b <= f a.
- by case: ltrgtP; try (by left); right.
- by left; apply: segment_injective_increasing.
right => x y xI yI.
suff : (- f) y <= (- f) x = (y <= x) by rewrite ler_oppl opprK.
apply: segment_injective_increasing xI => // [|x1 x2 x1I y1I U| x1 x1I].
- by rewrite ler_oppl opprK.
- by apply: fI => //; rewrite -[LHS]opprK [- f _]U opprK.
by apply/continuousN/fC.
Qed.

Lemma strict_to_large_itv (a b x : R) : x \in `]a, b[ -> x \in `[a, b].
Proof. by rewrite !in_itv /= => /andP[A B]; rewrite !le_eqVlt A B !orbT. Qed.

(* Maybe this belongs in normedtype. *)
Lemma near_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near y, z \in `]a, b[}.
Proof.
move=> y ayb; rewrite (near_shift 0 y).
have mingt0 : 0 < Num.min (y - a) (b - y).
  have : 0 < y - a by rewrite subr_gt0 (itvP ayb).
  have : 0 < b - y by rewrite subr_gt0 (itvP ayb).
  by case: (ltrP (y - a) (b - y)).
near=> z; rewrite /= subr0.
rewrite in_itv /= -ltr_subl_addl -ltr_subr_addl ltr_normlW /=; last first.
  rewrite normrN.
  by near: z; apply: nbhs0_lt; rewrite (lt_le_trans mingt0) // le_minl lexx.
rewrite -ltr_subr_addr ltr_normlW //.
near: z; apply: nbhs0_lt; rewrite (lt_le_trans mingt0) //.
by rewrite le_minl lexx orbT.
Grab Existential Variables. all: end_near. Qed.

Lemma near_0_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near 0 : R, (z + y : R) \in `]a, b[}.
Proof.
move=> y ayb.
rewrite (near_shift y 0); near=> z; rewrite /= sub0r subrK; near: z.
by rewrite near_simpl; apply: near_in_interval.
Grab Existential Variables. all: end_near. Qed.

Lemma left_inverse_increasing (a b : R) (f g : R -> R) :
  a < b -> f a <= f b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  Mf g (f a) (f b).
Proof.
move=> aLb faLfb ctf fK.
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
have fanfb : f a != f b.
  by apply/eqP=> fafb; move: (aLb); rewrite -(fK a) // fafb (fK b) // ltxx.
have ijf : If f a b by move=> x y xin yin fq; rewrite -(fK x) ?fq ?(fK y).
have incr := segment_injective_increasing faLfb ijf ctf.
have faLfb' : f a < f b.
  by rewrite lt_neqAle fanfb faLfb.
move=> x y xin yin.
have := IVT (ltW aLb) ctf; case: (ltrgtP (f a) (f b)) (faLfb')=> // _ _ ivt.
case: (ivt _ xin) => [u uin fux]; case: (ivt _ yin) => [v vin fvy].
by rewrite -fvy -fux; apply/esym; rewrite !fK //; apply: incr.
Qed.

Lemma interval_injective_continuous_bijective (a b : R) (f g : R -> R) :
 a < b ->
 {in `[a, b], continuous f} ->
 Mf f a b ->
 {in `[a, b], cancel f g} ->
 {in `[(f a), (f b)], cancel g f}.
Proof.
move=> aLb ctf monf fK y yin.
have faLfb' : f a <= f b by rewrite monf ?in_itv /= ?lexx ltW.
have := IVT (ltW aLb) ctf; case: (lerP (f a) (f b)) (faLfb')=> // _ _=> ivt.
by case: (ivt _ yin)=> x xin <-; rewrite fK.
Qed.
  
Lemma nearN (a : R) (P : R -> Prop) :
  (\forall x \near a,  P (- x)) <-> (\forall x \near (- a), P x).
Proof.
split; last by apply: opp_continuous.
case=> [e epos Pe]; exists e;[exact epos | ].
move=> z zclose; rewrite -(opprK z); apply: Pe.
by move: zclose; rewrite /ball_ /= -opprD normrN opprK.
Qed.

Lemma monotone_surjective_continuous (a b : R) (f g : R -> R) :
  a < b ->
  Mf f a b -> Mf g (f a) (f b) ->
  {in `[a, b], cancel f g} ->
  {in `[(f a), (f b)], cancel g f} ->
  {in `](f a), (f b)[, continuous g}.
Proof.
move=> aLb monf mong fK gK y yin; apply/cvg_distP=> _ /posnumP[e].
have faLfb : f a < f b.
  by rewrite (lt_trans (_ : f a <  y) _) // (itvP yin).
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
suff main : (forall (a b : R) (g f : R -> R) y, a < b -> f a < f b ->
         Mf f a b -> Mf g (f a) (f b) ->
         {in `[a, b], cancel f g} ->
         {in `[(f a), (f b)], cancel g f} ->
         y \in `](f a), (f b)[ ->
         \forall u \near y, u < y -> `|g y - g u| < e%:num).
  rewrite !near_simpl.
  have obLoa : -b < -a by rewrite ltr_oppl opprK.
  have ofbLofa : - f b < - f a by rewrite ltr_oppl opprK.
  have monof : Mf (-%R \o f \o -%R) (-b) (-a).
    move=> v w vin win; rewrite /= ler_oppl opprK monf ?oppr_itvcc //.
    by rewrite ler_oppl opprK.
  have monog : Mf (-%R \o g \o -%R) (- f b) (- f a).
    move=> v w vin win; rewrite /= ler_oppl opprK mong ?oppr_itvcc //.
    by rewrite ler_oppl opprK.
  have ofK : {in `[(-b), (-a)], cancel (-%R \o f \o -%R)(-%R \o g \o -%R)}.
    move=> v; rewrite -oppr_itvcc /= => vin.
    by rewrite opprK fK // opprK.
  have ogK : {in `[(- f b), (- f a)],
        cancel (-%R \o g \o -%R) (-%R \o f \o -%R)}.
    move=> v; rewrite -oppr_itvcc /= => vin.
    by rewrite opprK gK // opprK.    
  have oyin : -y \in `](- f b), (- f a)[ by rewrite oppr_itvoo !opprK.
  have := main _ _ (-%R \o g \o -%R)(-%R \o f \o -%R) (-y) obLoa.
    rewrite /= 2!opprK=> /(_ ofbLofa monof monog ofK ogK oyin) main'.
  near=> u; case: (ltrgtP u y); last 1 first.
  - by move=> ->; rewrite subrr normr0.
  - by near: u; rewrite near_simpl; apply: (main a b _ f).
  rewrite -(opprK y) -(opprK u) ltr_oppr -normrN opprD [in X in X -> _]opprK.
  near: u; rewrite near_simpl.
  by rewrite (nearN y (fun w => w < - y -> 
                `|- g(- - y) - - g (- w)| < e%:num)).
move=> {a b f g aLb faLfb aab bab monf mong fK gK y yin}. 
move=> a b g f y aLb faLfb monf mong fK gK yin.
have aab : a \in `[a, b] by rewrite in_itv /= lexx ltW.
have bab : b \in `[a, b] by rewrite in_itv /= lexx andbT ltW.
have fafafb : f a \in `[(f a), (f b)].
  by rewrite in_itv /= lexx ltW.
have gyLb : g y < b.
  by rewrite -(fK b) // ltNge mong ?(itvP yin) // strict_to_large_itv.
have aLgy : a < g y.
  by rewrite -(fK a) // ltNge mong // ?(itvP yin) ?strict_to_large_itv.
have gymeLgy : g y - e%:num < g y.
   by rewrite ltr_subl_addr ltr_addl.
case: (lerP a (g y - e%:num))=> [aLgyme | gymeLa ]; last first.
  have below : forall u, f a < u -> u < y -> `|g y - g u| < e%:num.
    move=> u aLu uLy.
    have uin : u \in `[(f a), (f b)].
      by rewrite in_itv /= ltW //= (ltW (lt_trans uLy _)) ?(itvP yin).
    have guLgy : g u <= g y.
      by rewrite mong //;[ rewrite ltW | rewrite strict_to_large_itv].
    move: (guLgy); rewrite -subr_ge0=> /ger0_norm => ->.
    rewrite ltr_subl_addr -ltr_subl_addl (lt_trans gymeLa) //.
    by rewrite ltNge -(fK a) // mong // -ltNge.
  near=> u; apply: below; suff h : u \in `](f a), (f b)[ by rewrite (itvP h).
  by near: u; apply: near_in_interval.
have below : forall u, f (g y - e%:num) < u -> u < y ->
     `|g y - g u| < e%:num.
  have gymein : g y - e%:num \in `[a, b].
    by rewrite in_itv /= aLgyme (le_trans _ (ltW gyLb)) // ler_subl_addl ler_addr.
  have faLfgyme : f a <= f (g y - e%:num) by rewrite monf.
  move=> u fgymeLu uLy.
  have uin : u \in `[(f a), (f b)].
    rewrite in_itv /= (ltW (lt_trans uLy _)) // ?andbT ?(itvP yin) //.
    by rewrite (le_trans faLfgyme) // ltW.
  have guLgy : g u <= g y.
    rewrite mong;[rewrite ltW //| | rewrite strict_to_large_itv //].
    rewrite in_itv /= (ltW (le_lt_trans _ fgymeLu)) /=.
      by rewrite (ltW (lt_trans uLy _)) // (itvP yin).
    by rewrite monf.
  move: (guLgy).
  rewrite -subr_ge0=> /ger0_norm=> ->; rewrite ltr_subl_addl -ltr_subl_addr.
  rewrite ltNge -monf //.
    by rewrite -ltNge gK //.
  rewrite in_itv /= -(fK a) ?mong // ltW //=.
    by rewrite (le_trans guLgy) // ltW.
  by rewrite (le_lt_trans faLfgyme fgymeLu).
near=> u; apply: below.
suff : u \in `]f (g y - e%:num), (f b)[ by move=> uin; rewrite (itvP uin).
near: u; apply: near_in_interval; rewrite in_itv /= ?(itvP yin) andbT.
rewrite -[X in _ < X](gK y); last by rewrite strict_to_large_itv.
rewrite ltNge monf -?ltNge //; first by rewrite in_itv /= (ltW aLgy) (ltW gyLb).
rewrite in_itv /= aLgyme /= (le_trans _ (ltW gyLb)) // ltW //.
Grab Existential Variables.  all:end_near. Qed.

Lemma inverse_increasing_continuous (a b : R) (f g : R -> R) : a < b ->
  f a <= f b ->
  {in `[a, b], continuous f} ->
  {in `[a, b], cancel f g} ->
  {in `](f a), (f b)[, continuous g}.
Proof.
move=> aLb faLfb' ctf fK.
have faLfb : f a < f b.
  rewrite lt_neqAle faLfb' andbT; apply/eqP=> fafb.
  by move: (aLb); rewrite -(fK a) ?fafb ?fK ?ltxx // ?in_itv /= lexx (ltW aLb).
have ivt : {in `](f a), (f b)[, forall y, exists2 x, a < x < b & y = f x}.
  move=> y yin.
  have yin' : y \in `[(f a), (f b)] by rewrite strict_to_large_itv.
  have := IVT (ltW aLb) ctf; case: (ltrgtP (f a) (f b)) (faLfb)=> // _ _.
  move=> /(_ _ yin')=> [][] c; rewrite in_itv /= !le_eqVlt=> /andP[].
  move=> /orP[/eqP <- |aLc].
    by move=> _ fay; move: yin; rewrite -fay in_itv /= ltxx.
  move=> /orP[/eqP -> |cLb].
    by move=> fy; move: yin; rewrite -fy in_itv /= ltxx andbF.
  by move=> <-; exists c; rewrite ?aLc ?cLb.
have ifab : If f a b.
  by rewrite /If=> u v uin vin fufv; rewrite -(fK u uin) fufv fK.
have [incrf | abs] := segment_injective_monotone ifab ctf; last first.
  move: (abs a b); rewrite !in_itv /= !lexx ltW // ltW // leNgt aLb.
  by move=> /(_ isT isT).
have incrg := left_inverse_increasing aLb faLfb' ctf fK.
have gK := interval_injective_continuous_bijective aLb ctf incrf fK.
by apply: monotone_surjective_continuous.
Qed.

Lemma subset_ball_prop_in_itv (x : R) e P :
  (ball_ [eta Num.Def.normr] x e `<=` P)%classic <->
  {in  `](x - e), (x + e)[ , forall y, P y}.
Proof.
split.
  move=> bp y; rewrite in_itv/= => yin; apply: bp=> /=.
  by rewrite distrC ltr_distl.
by move=> inxep y /= inball; apply: inxep; rewrite in_itv/= -ltr_distl distrC.
Qed.

Lemma prop_in_and (p : mem_pred R) (P Q : R -> Prop) :
  {in p, forall x, P x /\ Q x} <->
  {in p, forall x, P x} /\ {in p, forall x, Q x}.
Proof.
split.
  by move=> cnd; split; move=> x xin; case: (cnd x xin).
by move=> [cnd1 cnd2] x xin; split;[apply: cnd1 | apply: cnd2].
Qed.

Lemma subset_prop_in1 (T : Type) (E E': mem_pred T) (P : T -> Prop):
  {subset E <= E'} -> {in E', forall x, P x} ->
  {in E, forall x, P x}.
Proof. by move=> sub p' x xE; apply/p'/sub. Qed.

Ltac staged_split :=
  repeat (rewrite andb_idr;[ | move=> *]).

(* This is an example that appears in the following proof.  I think
  there could be a use case for tactic that leads the user to proving
  a conjunction by addressing the second component with the assumption
  that the first one already holds. *)
Fact itv_example (x e  : R):
  0 < e -> [&& x < x + e, x - e < x & x - e < x + e].
Proof.
move=> e0; staged_split;[rewrite ltr_addl // | rewrite ltr_subl_addr //| ].
(* Unfortunately, the name of the hypotheses could be useful here. *)
eapply lt_trans; eassumption.
Qed.

Lemma continuous_inverse  (f g : R -> R) (x : R) :
  {near x, cancel f g} -> {near x, continuous f} -> {near (f x), continuous g}.
Proof.
(* The first 3 lines to get the left inverse and the continuity in the       *)
(*  same ball, and then transform this ball into an interval.                *)
move=> fK ctf; have := conj fK ctf => {fK ctf}.
rewrite -(near_andP (F := nbhs x)) near_simpl.
case=> [e' e'gt0]/subset_ball_prop_in_itv/prop_in_and [fK ctf].
(* We then need a non-singleton closed interval containing x inside the      *)
(* ball.                                                                     *)
set e := e' / 2.
have e0 : 0 < e by apply: divr_gt0.
have elte' : e < e'.
  by rewrite (@ltr_pdivr_mulr _ 2) // !mulr_natr mulrS mulr1n ltr_addl.
have itvsub  : {subset `[(x - e), (x + e)] <=  `](x - e'), (x + e')[}.
  apply/subitvP.
  by rewrite subitvE /Order.le /= !ltr_add2l ltr_oppl opprK elte'.
have fK' : {in `[x - e, x + e], cancel f g}.
  by apply/(subset_prop_in1 itvsub fK).
have ctf' : {in `[x - e, x + e], continuous f}.
  by apply/(subset_prop_in1 itvsub ctf).
have /and3P[cmp2 [cmp1 cmp]] : [&& x < x + e, x - e < x & x - e < x + e].
  by rewrite !(ltr_subl_addr, ltr_addl, ltr_spsaddr) e0.
have ifx : If f (x - e) (x + e).
  by move=> v w vin win fq; rewrite -(fK' v) // fq fK'.
have [mfx |mfx] := segment_injective_monotone ifx ctf'.
  near=> z; apply: inverse_increasing_continuous ctf' _ _ _ => //.
    by rewrite mfx ?ltW // in_itv /= ?lexx ltW.
  near: z; rewrite near_simpl; apply: near_in_interval.
  by rewrite in_itv /= !(ltNge, mfx, in_itv) /= -?ltNge ?(lexx, cmp1, ltW).
near=> y; rewrite -[y]opprK (_ : g = (g \o -%R \o -%R)); last first.
  by apply: funext=> u; rewrite /= opprK.
apply: continuous_comp; rewrite opprK; first by apply: continuousN.
have ctNf: {in `[(x - e), (x + e)], continuous (- f)}.
  by move=> z zI; apply/continuousN/ctf'.
apply: inverse_increasing_continuous ctNf _ _ _ => //.
- by rewrite lter_oppr opprK mfx ?ltW // in_itv /= ?lexx ltW.
- by move=> z zI; rewrite /= opprK fK'.
rewrite oppr_itvoo !opprK.
near: y; rewrite near_simpl; apply: near_in_interval.
by rewrite in_itv /= !(ltNge, mfx, in_itv) /= -?ltNge ?(lexx, cmp2, ltW).
Grab Existential Variables. all:end_near. Qed.


Lemma sqr_continuous : continuous (exprz (R := R) ^~ 2).
Proof.
move => x s.
rewrite (_ : (fun x => x ^ 2) = fun x : R => x * x); last first.
  by  apply: funext=> y; rewrite exprSz expr1z.
by rewrite exprSz expr1z; apply: continuousM.
Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x.
case: (ltrgtP x 0) => [xlt0 | xgt0 | ->].
- apply: (near_cst_continuous 0).
  rewrite (near_shift 0 x).
  near=> z; rewrite subr0 /=; apply: ltr0_sqrtr.
  rewrite -(opprK x) subr_lt0; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; rewrite ltr_oppr oppr0.
- have csqr bnd : 0 < bnd -> {in `[0, bnd], continuous (exprz (R := R) ^~ 2)}.
  by move=> bndgt0 u _; apply: sqr_continuous.
  have xp1gt0 : 0 < Num.sqrt (x + 1) by rewrite sqrtr_gt0 addr_gt0.
  have xp1gt0' : 0 < x + 1 by rewrite addr_gt0.
  have m01' : Num.min 0 (x + 1) = 0 by case: (ltrgtP 0 (x + 1)) xp1gt0'.
  have M01' : Num.max 0 (x + 1) = (x + 1) by case: (ltrgtP 0 (x + 1)) xp1gt0'. 
  have ctf := csqr _ xp1gt0.
  apply: (inverse_continuous xp1gt0 ctf).
  move=> u; rewrite sqrtr_sqr => uin; apply/normr_idP.
  by rewrite (itvP uin).
  rewrite /exprz /= ?addn1 sqr_sqrtr ?expr0n /=; last first.
    by rewrite addr_ge0 // ltW.
  by rewrite in_itv m01' M01' /= xgt0 cpr_add ltr01.
apply/cvg_distP=> _ /posnumP[e]; rewrite !near_simpl /=.
near=> y; rewrite sqrtr0 sub0r normrN.
rewrite ger0_norm ?sqrtr_ge0 //.
have ylte2 : y < e%:num ^+ 2.
  rewrite ltr_normlW //; near: y; apply: nbhs0_lt.
  by rewrite exprn_gt0.
have twogt0 : (0 < 2)%N by [].
rewrite -(ltr_pexpn2r twogt0) ?inE ?nnegrE ?ltrW ?sqrtr_ge0 //.
have [ylt0 | ] := boolP(y < 0).
  by rewrite ltr0_sqrtr // expr0n /= exprn_gt0.
by rewrite -leNgt => yge0; rewrite sqr_sqrtr.
Grab Existential Variables. all: end_near. Qed.

End real_inverse_functions.
