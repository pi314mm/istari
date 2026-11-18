Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Uniform.
Require Import Intensional.
Require Import Candidate.
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import Shut.
Require Import Defined.
Require Import Page.
Require Import PageCode.
Require Import Extend.
Require Import Truncate.
Require Import ExtendTruncate.
Require Import ProperLevel.
Require Import ProperDownward.
Require Import SemanticsUniv.
Require Import SemanticsFut.
Require Import SemanticsSet.
Require Import SemanticsSigma.
Require Import SemanticsEqual.
Require Import SemanticsProperty.
Require Import Urelsp.
Require Import SemanticsSimple.


(* Soundness of the rule futureUnivSurj:

     G |- {exists (x : univ I) . M = next x : future (univ I)}
     >>
     G |- {exists (x : univ I) . M = next x : future (univ I)} : type
     G |- M : future (univ I)

   Notation used in the comments below:

     m ~ n in R @ i    means   rel (den R) i m n
     a => R            means   the term a is interpreted as the semantic
                               type R (interp/basic/sint)
     U_j               means   iuuniv the_system j gpg, the universe at
                               page gpg (the page lv denotes) at stage j
     fut (S j) R       means   iufut stop (S j) R; its elements at stage
                               S j are terms that evaluate to next m'
                               with m' an element of R at stage j

   Outline of the proof:

   1. Unfold the judgements: fix a stage i and substitutions s, s'.  We
      must show triv ~ triv in R @ i, where R interprets the squashed
      sigma type C.

   2. Take R apart: squash is a set over unit, whose predicate is the
      sigma type over U_i of the equality type.

   3. The main step: find a type T in U_i such that m = next T in
      fut (univ lv) at stage i.
        - At stage 0 nothing is required beneath next, so T = unittp.
        - At stage S j, m evaluates to next m1, where m1 is a type at
          stage j interpreted as some R0.  The witness is extt R0, the
          semantic constant for R0, which is a closed term that is a
          type at every stage.

   4. Assemble <T, triv> as the inhabitant of the sigma type, which
      shows that the set predicate holds of triv. *)


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


(* Every type available one step later is next of a type available now.
   The witness is the semantic constant extt applied to the type's
   interpretation one step later.  At stage S j, extt R0 means R0 cut off
   at stage S (S j), which agrees with R0 at stage j. *)
Lemma sound_fut_univ_surj :
  forall G lv m,
    pseq G (deqtype
              (squash (sigma (univ lv) (equal (fut (univ (subst sh1 lv))) (subst sh1 m) (next (var 0)))))
              (squash (sigma (univ lv) (equal (fut (univ (subst sh1 lv))) (subst sh1 m) (next (var 0))))))
    -> pseq G (deq m m (fut (univ lv)))
    -> pseq G (deq triv triv
                 (squash (sigma (univ lv) (equal (fut (univ (subst sh1 lv))) (subst sh1 m) (next (var 0)))))).
Proof.
intros G lv m.
revert G.
(* Change pseq (judgements in all contexts) to seq (judgements in a
   given context G).  The rule has no hygiene premises and two judgement
   premises. *)
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G HseqC Hseqm.
(* Unfold the semantic meaning of the judgements.  HseqC says that the
   squashed sigma type (call it C) is a type, Hseqm says that
   m : fut (univ lv), and the goal is triv : C. *)
rewrite -> seq_eqtype in HseqC.
rewrite -> seq_deq in Hseqm |- *.
(* Fix a stage i and substitutions s, s' that are related at stage i. *)
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
(* C under s (and under s') is interpreted as R. *)
so (HseqC _#3 Hs) as (R & Hl & Hr & _ & _).
(* fut (univ lv) under s is interpreted as F, and m[s] ~ m[s'] in F @ i
   (Hm). *)
so (Hseqm _#3 Hs) as (F & Hfl & _ & Hm & _ & _).
clear HseqC Hseqm.
(* Use R as the interpretation of C in the goal.  Except for
   triv ~ triv in R @ i, everything holds by Hl and Hr. *)
exists R.
cut (rel (den R) i triv triv).
  {
  intro H.
  do2 4 split; auto; simpsub; auto.
  }
(* Step 2: take R apart.  squash C' is defined as set unittp C', so R is
   iuset (unit) B for a family B over unit. *)
unfold squash in Hl.
simpsubin Hl.
simpsubin Hfl.
invert (basic_value_inv _#6 value_set Hl).
intros A B HA HB <-.
invert (basic_value_inv _#6 value_unittp HA).
intros <-.
(* triv is an element of unit at stage i. *)
assert (rel (den (iubase (unit_urel stop i))) i triv triv) as Htriv.
  {
  cbn.
  do2 4 split; auto using star_refl; prove_hygiene.
  }
(* The fiber of B at triv is the sigma type
   sigma (univ lv) (equal (fut (univ lv)) m (next (var 0))) under s. *)
invert HB.
intros _ _ Hact.
so (Hact i triv triv (le_refl _) Htriv) as Hsig.
simpsubin Hsig.
invert (basic_value_inv _#6 value_sigma Hsig).
intros U B2 HU HB2 HeqB.
(* The first component of the sigma is univ lv, interpreted as U_i,
   where gpg is the page that lv[s] denotes. *)
invert (basic_value_inv _#6 value_univ HU).
intros gpg Hlv _ _ <-.
(* Step 3, the main step: find T in U_i such that m = next T in F at
   stage i.  By the definition of the equality type, that means
     m[s] ~ next T in F @ i   and   next T ~ next T in F @ i. *)
assert (exists T (HT : rel (den (iuuniv the_system i gpg)) i T T),
          rel (den F) i (subst s m) (next T)
          /\ rel (den F) i (next T) (next T)) as (T & HT & HmT & HTT).
  {
  clear Hact Hsig HeqB HB2 HU Hl Hr HB HA.
  destruct i as [| j].
    {
    (* Stage 0.  Here fut (univ lv) is interpreted as iufut0, which only
       requires both sides to evaluate to next of something; nothing is
       required of what is under next.  So any type works as T; we use
       unittp. *)
    invert (basic_value_inv _#6 value_fut Hfl).
    intros _ <-.
    cbn in Hm.
    (* m[s] evaluates to next m1. *)
    destruct Hm as (m1 & m1' & _ & Hclm & _ & Hstep & _ & _).
    (* unittp is in U_0: both sides interpret it as unit. *)
    assert (rel (den (iuuniv the_system 0 gpg)) 0 unittp unittp) as HT.
      {
      cbn.
      split; auto.
      exists (iubase (unit_urel stop 0)).
      rewrite -> sint_unroll.
      split; apply interp_eval_refl; apply interp_unit.
      }
    exists unittp, HT.
    split.
      {
      (* m[s] ~ next unittp: m[s] evaluates to next m1, next unittp is
         already a value, and at stage 0 nothing is required of m1 and
         unittp (the condition 0 > 0 is impossible). *)
      cbn.
      exists m1, unittp.
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }

      {
      (* next unittp ~ next unittp, by the same reasoning. *)
      cbn.
      exists unittp, unittp.
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }
    }
  (* Stage S j.  F is iufut (S j) U, where U is the interpretation of
     univ lv at stage j.  That is U_j, for the same page gpg, since a
     level term denotes at most one page (pginterp_fun). *)
  invert (basic_value_inv _#6 value_fut Hfl).
  intros U HU0 <-.
  invert (basic_value_inv _#6 value_univ HU0).
  intros gpg' Hlv' _ _ <-.
  so (pginterp_fun _#3 Hlv Hlv'); subst gpg'.
  (* m[s] evaluates to next m1, and since S j > 0 we have m1 ~ m1' in
     U_j @ j.  So m1 is a type at stage j, interpreted as some R1. *)
  cbn in Hm.
  destruct Hm as (m1 & m1' & _ & Hclm & _ & Hstep & _ & Hrel).
  exploit Hrel as Hrel'; [omega |].
  clear Hrel.
  cbn in Hrel'.
  destruct Hrel' as (_ & R1 & HR1 & _).
  rewrite -> sint_unroll in HR1.
  (* Types in a universe at page gpg are interpreted at level cin gpg:
     R1 = extend R0 for some R0 : wiurel (cin gpg). *)
  so (interp_level_internal _#5 (cin_stop gpg) HR1) as (R0 & ->).
  (* cin gpg is strictly below stop (since cin gpg <= top < succ top = stop),
     which is what we need to make R0 into a semantic object. *)
  assert (cin gpg << stop) as h.
    {
    exact (le_lt_ord_trans _#3 (cin_top gpg) (succ_increase top)).
    }
  (* The witness: T is extt R0, the semantic constant for R0, which is a
     closed term. *)
  set (T := @extt (Candidate.obj stop) (objin (objsome (expair (qtype (cin gpg)) R0) h))).
  (* At every stage k (and on either side b), T is interpreted as R0 cut
     off at stage S k (rule interp_extt). *)
  assert (forall b k,
            interp gpg b k T
              (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S k) R0))) as HTint.
    {
    intros b k.
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  (* m1's interpretation agrees with T's interpretation at stage j.  Every
     interpretation at stage j is already cut off at stage S j
     (basic_impl_iutruncate), so extend R0 = extend (iutruncate (S j) R0).
     The two proofs of cin gpg <<= stop are equal by proof irrelevance. *)
  assert (extend_iurel (cin_stop gpg) R0
          = extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S j) R0)) as HeqR0.
    {
    so (basic_impl_iutruncate _#6 HR1) as H.
    rewrite -> iutruncate_extend_iurel in H.
    rewrite -> H.
    f_equal.
    apply proof_irrelevance.
    }
  assert (hygiene clo T) as HclT.
    {
    apply hygiene_auto; cbn; auto.
    }
  (* T is in U_(S j) at stage S j: both sides interpret it as the same
     type (HTint at stage S j). *)
  assert (rel (den (iuuniv the_system (S j) gpg)) (S j) T T) as HT.
    {
    cbn.
    split; auto.
    exists (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S (S j)) R0)).
    rewrite -> sint_unroll.
    auto.
    }
  exists T, HT.
  split.
    {
    (* m[s] ~ next T in fut (S j) U_j @ S j.  m[s] evaluates to next m1,
       next T is already a value, and m1 ~ T in U_j @ j because m1 is
       interpreted as extend R0 (HR1) and T is interpreted as the same
       type (HTint at stage j, rewritten by HeqR0). *)
    cbn.
    exists m1, T.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intros _.
    cbn.
    split; auto.
    exists (extend_iurel (cin_stop gpg) R0).
    rewrite -> sint_unroll.
    split; auto.
    rewrite -> HeqR0.
    auto.
    }

    {
    (* next T ~ next T in fut (S j) U_j @ S j: T ~ T in U_j @ j, since
       both sides interpret T as R0 cut off at stage S j (HTint). *)
    cbn.
    exists T, T.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intros _.
    cbn.
    split; auto.
    exists (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S j) R0)).
    rewrite -> sint_unroll.
    auto.
    }
  }
(* Step 4: build the inhabitant.  The fiber of the sigma's family B2 at T
   is the equality type equal (fut (univ lv)) m (next T), whose
   underlying type is interpreted as F (basic_fun with Hfl). *)
invert HB2.
intros _ _ Hact2.
so (Hact2 i T T (le_refl _) HT) as Heq.
simpsubin Heq.
invert (basic_value_inv _#6 value_equal Heq).
intros p q A Hmp Hnq HA' HeqB2.
so (basic_fun _#7 HA' Hfl); subst A.
(* triv ~ triv in the set type: triv is in unit (Htriv), and the set's
   predicate (the fiber of B at triv) is inhabited by the pair <T, triv>. *)
cbn.
exists (ppair T triv), (ppair T triv), Htriv.
cbn.
(* Replace the fiber of B at triv by the sigma type (HeqB). *)
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iusigma stop (iuuniv the_system i gpg) B2) by exact HeqB
end.
cbn.
(* <T, triv> ~ <T, triv> in the sigma type: the first components are
   related by HT, both sides are already pairs, and it remains to show
   triv ~ triv in the fiber of B2 at T. *)
exists T, T, triv, triv, HT.
so (urel_closed _#5 HT) as (HclT & _).
do2 4 split; auto using star_refl; try prove_hygiene.
(* Replace the fiber of B2 at T by the equality type (HeqB2).  triv ~ triv
   there holds because both m[s] and next T are related to next T in F
   (HmT and HTT). *)
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iuequal stop true i F (subst s m) (next T) p q Hmp Hnq) by exact HeqB2
end.
cbn.
do2 5 split; auto using star_refl; try prove_hygiene.
Qed.
