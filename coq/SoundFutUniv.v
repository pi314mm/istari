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
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G HseqC Hseqm.
rewrite -> seq_eqtype in HseqC.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (HseqC _#3 Hs) as (R & Hl & Hr & _ & _).
so (Hseqm _#3 Hs) as (F & Hfl & _ & Hm & _ & _).
clear HseqC Hseqm.
exists R.
cut (rel (den R) i triv triv).
  {
  intro H.
  do2 4 split; auto; simpsub; auto.
  }
unfold squash in Hl.
simpsubin Hl.
simpsubin Hfl.
invert (basic_value_inv _#6 value_set Hl).
intros A B HA HB <-.
invert (basic_value_inv _#6 value_unittp HA).
intros <-.
assert (rel (den (iubase (unit_urel stop i))) i triv triv) as Htriv.
  {
  cbn.
  do2 4 split; auto using star_refl; prove_hygiene.
  }
invert HB.
intros _ _ Hact.
so (Hact i triv triv (le_refl _) Htriv) as Hsig.
simpsubin Hsig.
invert (basic_value_inv _#6 value_sigma Hsig).
intros U B2 HU HB2 HeqB.
invert (basic_value_inv _#6 value_univ HU).
intros gpg Hlv _ _ <-.
assert (exists T (HT : rel (den (iuuniv the_system i gpg)) i T T),
          rel (den F) i (subst s m) (next T)
          /\ rel (den F) i (next T) (next T)) as (T & HT & HmT & HTT).
  {
  clear Hact Hsig HeqB HB2 HU Hl Hr HB HA.
  destruct i as [| j].
    {
    invert (basic_value_inv _#6 value_fut Hfl).
    intros _ <-.
    cbn in Hm.
    destruct Hm as (m1 & m1' & _ & Hclm & _ & Hstep & _ & _).
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
      cbn.
      exists m1, unittp.
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }

      {
      cbn.
      exists unittp, unittp.
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }
    }
  invert (basic_value_inv _#6 value_fut Hfl).
  intros U HU0 <-.
  invert (basic_value_inv _#6 value_univ HU0).
  intros gpg' Hlv' _ _ <-.
  so (pginterp_fun _#3 Hlv Hlv'); subst gpg'.
  cbn in Hm.
  destruct Hm as (m1 & m1' & _ & Hclm & _ & Hstep & _ & Hrel).
  exploit Hrel as Hrel'; [omega |].
  clear Hrel.
  cbn in Hrel'.
  destruct Hrel' as (_ & R1 & HR1 & _).
  rewrite -> sint_unroll in HR1.
  so (interp_level_internal _#5 (cin_stop gpg) HR1) as (R0 & ->).
  assert (cin gpg << stop) as h.
    {
    exact (le_lt_ord_trans _#3 (cin_top gpg) (succ_increase top)).
    }
  set (T := @extt (Candidate.obj stop) (objin (objsome (expair (qtype (cin gpg)) R0) h))).
  assert (forall b k,
            interp gpg b k T
              (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S k) R0))) as HTint.
    {
    intros b k.
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
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
invert HB2.
intros _ _ Hact2.
so (Hact2 i T T (le_refl _) HT) as Heq.
simpsubin Heq.
invert (basic_value_inv _#6 value_equal Heq).
intros p q A Hmp Hnq HA' HeqB2.
so (basic_fun _#7 HA' Hfl); subst A.
cbn.
exists (ppair T triv), (ppair T triv), Htriv.
cbn.
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iusigma stop (iuuniv the_system i gpg) B2) by exact HeqB
end.
cbn.
exists T, T, triv, triv, HT.
so (urel_closed _#5 HT) as (HclT & _).
do2 4 split; auto using star_refl; try prove_hygiene.
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iuequal stop true i F (subst s m) (next T) p q Hmp Hnq) by exact HeqB2
end.
cbn.
do2 5 split; auto using star_refl; try prove_hygiene.
Qed.
