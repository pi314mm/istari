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

Require Import Model.
Require Import Standard.
Require Import Ceiling.
Require Import SoundUtil.
Require Import MapTerm.
Require Import SemanticsPi.


(* A semantic constant for a family of types over D, at level w. *)
Definition famobj w (D : wurel w) (G : urelsp D -n> wiurel_ofe w)
  (h : level (qtarrow w D (qtype w)) << stop) : sterm :=
  ext (objin (objsome (expair (qtarrow w D (qtype w)) G) h)).


Lemma ctapp_famobj :
  forall pg w (D : wurel w) (G : urelsp D -n> wiurel_ofe w) (h : level (qtarrow w D (qtype w)) << stop) (s : bool) j (m : sterm) (n p : wterm w) (Hnp : rel D j n p),
    w <<= cin pg
    -> map_term (extend stop w) m = (if s then n else p)
    -> cbasic the_system pg s j (ctapp (famobj w D G h) m)
         (expair (qtype w) (iutruncate (S j) (pi1 G (urelspinj D j n p Hnp)))).
Proof.
intros pg w D G h s j m n p Hnp Hw Hm.
set (Hnp' := conj (Nat.lt_succ_diag_r j) Hnp : rel (ceiling (S j) D) j n p).
replace (iutruncate (S j) (pi1 G (urelspinj D j n p Hnp)))
  with (pi1 (proj j (qtarrow w D (qtype w)) (std (S j) (qtarrow w D (qtype w)) G))
          (urelspinj (ceiling (S j) D) j n p Hnp')).
  {
  apply cinterp_eval_refl.
  apply (interp_ctapp _#6 w (ceiling (S j) D) (qtype w)
           (proj j (qtarrow w D (qtype w)) (std (S j) (qtarrow w D (qtype w)) G))
           n p Hnp'); auto.
  apply cinterp_eval_refl.
  apply interp_ext.
  cbn.
  rewrite -> max_ord_id.
  auto.
  }
unfold proj.
cbn.
subst Hnp'.
rewrite -> embed_ceiling_urelspinj.
rewrite -> std_tarrow_is.
cbn.
unfold std_tarrow_action.
rewrite -> urelsp_index_inj.
rewrite -> Nat.min_id.
cbn.
reflexivity.
Qed.


(* A family of types at level w over D, from a family Bf of top-level
   types over D cut off at stage k, each of which comes from level w.
   Elements of D at stages above k are sent to their stage k part. *)
Lemma make_family :
  forall w (h : w <<= stop) k (D : wurel w)
    (Bf : urelsp (extend_urel w stop (ceiling (S k) D)) -n> siurel_ofe),
    (forall C, exists R0, pi1 Bf C = extend_iurel h R0)
    -> exists (G : urelsp D -n> wiurel_ofe w),
         forall C,
           extend_iurel h (pi1 G C)
           = pi1 Bf (extend_urelsp h _ (proj_ceiling (S k) (Nat.lt_0_succ k) D C)).
Proof.
intros w h k D Bf Hext.
set (F := nearrow_compose Bf
            (nearrow_compose (extend_urelsp_ne h (ceiling (S k) D))
               (proj_ceiling_ne (S k) (Nat.lt_0_succ k) D))).
assert (forall C, exists! R0, pi1 F C = extend_iurel h R0) as Huniq.
  {
  intros C.
  so (Hext (pi1 (nearrow_compose (extend_urelsp_ne h (ceiling (S k) D))
                   (proj_ceiling_ne (S k) (Nat.lt_0_succ k) D)) C)) as (R0 & HR0).
  exists R0.
  split; auto.
  intros R1 HR1.
  apply (extend_iurel_inj _ _ h).
  rewrite <- HR0, <- HR1.
  reflexivity.
  }
so (choice _#3 Huniq) as (g & Hg).
assert (@nonexpansive (urelsp D) (wiurel_ofe w) g) as Hne.
  {
  intros n C C' Hdist.
  apply (extend_iurel_noncontractive _ _ h).
  rewrite <- !Hg.
  apply (pi2 F).
  exact Hdist.
  }
exists (expair g Hne).
intro C.
cbn.
rewrite <- Hg.
reflexivity.
Qed.


Lemma subst_famobj :
  forall (s : ssub) w D G h, subst s (famobj w D G h) = famobj w D G h.
Proof.
intros.
unfold famobj.
apply subst_ext.
Qed.


Lemma famobj_closed :
  forall w D G h, hygiene clo (famobj w D G h).
Proof.
intros.
unfold famobj.
apply hygiene_auto; cbn; auto.
Qed.


(* The witness: an element of A -> U i that agrees with y0 up to stage k
   and is an element at stage S k.  X is A's interpretation at level
   cin gpg, Bp and Bk are the constant families of U i in the arrow types
   at stages S k and k. *)
Lemma arrow_univ_witness :
  forall gpg lv k (X : wiurel (cin gpg))
    (Bp : urelsp (den (extend_iurel (cin_stop gpg) X)) -n> siurel_ofe)
    (Bk : urelsp (den (extend_iurel (cin_stop gpg) (iutruncate (S k) X))) -n> siurel_ofe)
    y0 y0',
    pginterp lv gpg
    -> hygiene clo lv
    -> (forall j n n' Hn, pi1 Bp (urelspinj _ j n n' Hn) = iuuniv the_system j gpg)
    -> (forall j n n' Hn, pi1 Bk (urelspinj _ j n n' Hn) = iuuniv the_system j gpg)
    -> rel (den (iupi stop k (extend_iurel (cin_stop gpg) (iutruncate (S k) X)) Bk)) k y0 y0'
    -> exists T,
         rel (den (iupi stop (S k) (extend_iurel (cin_stop gpg) X) Bp)) (S k) T T
         /\ rel (den (iupi stop k (extend_iurel (cin_stop gpg) (iutruncate (S k) X)) Bk)) k y0 T
         /\ rel (den (iupi stop k (extend_iurel (cin_stop gpg) (iutruncate (S k) X)) Bk)) k T T.
Proof.
intros gpg lv k X Bp Bk y0 y0' Hlv Hcllv HBp HBk Hy0.
set (w := cin gpg).
set (h := cin_stop gpg).
cbn in Hy0.
destruct Hy0 as (l & l' & _ & Hcly0 & Hcly0' & Hstep & Hstep' & Hact).
assert (hygiene (permit clo) l) as Hcll.
  {
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstep Hcly0)) as H; cbn in H.
  destruct H; auto.
  }
assert (hygiene (permit clo) l') as Hcll'.
  {
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstep' Hcly0')) as H; cbn in H.
  destruct H; auto.
  }
set (Ak := extend_iurel h (iutruncate (S k) X)).
assert (den Ak = ceiling (S k) (den Ak)) as HeqAk.
  {
  apply urel_extensionality.
  fextensionality 3.
  intros j m p.
  cbn.
  pextensionality; [intros (Hj & H); split; auto; omega | tauto].
  }
exploit (extract_functional gpg k (den Ak) l l') as (Bf & Hbf & _); auto.
  {
  intros j m p Hmp.
  assert (j <= k) as Hj.
    {
    destruct Hmp as (Hj & _).
    omega.
    }
  so (Hact j m p Hj Hmp) as H.
  rewrite -> HBk in H.
  destruct H as (_ & R & HR & HR').
  rewrite -> sint_unroll in HR, HR'.
  eauto.
  }
assert (forall C, exists R0, pi1 Bf C = extend_iurel h R0) as Hext.
  {
  intro C.
  so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
  invert Hbf.
  intros _ _ Hfun.
  assert (j <= k) as Hj.
    {
    destruct Hmp as (Hj & _).
    omega.
    }
  so (Hfun j m p Hj Hmp) as H.
  exact (interp_level_internal _#5 h H).
  }
so (make_family w h k (den X) Bf Hext) as (G & HG).
assert (level (qtarrow w (den X) (qtype w)) << stop) as hq.
  {
  cbn.
  rewrite -> max_ord_id.
  exact (le_lt_ord_trans _#3 (cin_top gpg) (succ_increase top)).
  }
set (Q := famobj w (den X) G hq).
set (body := con lv (ctapp Q (var 0))).
assert (forall n, subst1 n body = con lv (ctapp Q n)) as Hbody.
  {
  intro n.
  unfold body.
  simpsub.
  unfold subst1.
  rewrite -> (subst_into_closed _ _ lv Hcllv).
  unfold Q.
  rewrite -> subst_famobj.
  reflexivity.
  }
assert (forall (b : bool) j (n n' : sterm)
          (Hn : rel (den X) j (map_term (extend stop w) n) (map_term (extend stop w) n')),
          interp gpg b j (con lv (ctapp Q (if b then n else n')))
            (extend_iurel h (iutruncate (S j) (pi1 G (urelspinj (den X) j _ _ Hn))))) as Hcon.
  {
  intros b j n n' Hn.
  apply interp_eval_refl.
  apply interp_con; auto using le_page_refl.
  apply ctapp_famobj.
    {
    apply le_ord_refl.
    }
  destruct b; reflexivity.
  }
assert (hygiene clo (lam body)) as HclT.
  {
  unfold body, Q.
  so (famobj_closed w (den X) G hq).
  prove_hygiene.
  }
clearbody body Q.
assert (forall i' (D' : wiurel stop) (B' : urelsp (den D') -n> siurel_ofe),
          (forall j n n', rel (den D') j n n'
                          -> rel (den X) j (map_term (extend stop w) n) (map_term (extend stop w) n'))
          -> (forall j n n' Hn, pi1 B' (urelspinj _ j n n' Hn) = iuuniv the_system j gpg)
          -> rel (den (iupi stop i' D' B')) i' (lam body) (lam body)) as HTT.
  {
  intros i' D' B' HD' HB'.
  cbn.
  exists body, body.
  do2 5 split; auto using star_refl.
  intros j n n' Hj Hn.
  rewrite -> HB'.
  cbn.
  split; auto.
  exists (extend_iurel h (iutruncate (S j) (pi1 G (urelspinj (den X) j _ _ (HD' _ _ _ Hn))))).
  rewrite -> sint_unroll.
  rewrite -> !Hbody.
  split.
    {
    exact (Hcon true j n n' (HD' _ _ _ Hn)).
    }

    {
    exact (Hcon false j n n' (HD' _ _ _ Hn)).
    }
  }
exists (lam body).
do2 2 split.
  {
  apply HTT; auto.
  }

  {
  cbn.
  exists l, body.
  do2 5 split; auto using star_refl.
  intros j n n' Hj Hn.
  rewrite -> HBk.
  cbn.
  split; auto.
  invert Hbf.
  intros _ _ Hfun.
  exists (pi1 Bf (urelspinj (den Ak) j n n' Hn)).
  rewrite -> sint_unroll.
  split.
    {
    exact (Hfun j n n' Hj Hn).
    }
  rewrite -> Hbody.
  replace (pi1 Bf (urelspinj (den Ak) j n n' Hn))
    with (extend_iurel h (iutruncate (S j) (pi1 G (urelspinj (den X) j _ _ (proj2 Hn))))).
    {
    exact (Hcon false j n n' (proj2 Hn)).
    }
  rewrite <- iutruncate_extend_iurel.
  rewrite -> HG.
  assert (extend_urelsp h (ceiling (S k) (den X))
            (proj_ceiling (S k) (Nat.lt_0_succ k) (den X) (urelspinj (den X) j _ _ (proj2 Hn)))
          = urelspinj (den Ak) j n n' Hn) as Heqc.
    {
    apply exT_extensionality_prop.
    cbn.
    fextensionality 2.
    intros i' z.
    pextensionality.
      {
      intros (Hi' & Hi'' & Hz).
      do2 2 split; auto.
      }

      {
      intros (Hi' & Hi'' & Hz).
      do2 2 split; auto; omega.
      }
    }
  transitivity (iutruncate (S j) (pi1 Bf (urelspinj (den Ak) j n n' Hn))).
    {
    f_equal.
    f_equal.
    exact Heqc.
    }
  symmetry.
  exact (basic_impl_iutruncate _#6 (Hfun j n n' Hj Hn)).
  }

  {
  apply HTT; auto.
  intros j n n' Hn.
  exact (proj2 Hn).
  }
Qed.


(* Every function into U i available one step later is next of one
   available now.  The witness is built by arrow_univ_witness. *)
Lemma sound_fut_arrow_univ_surj :
  forall G a lv y,
    pseq G (deq a a (univ lv))
    -> pseq G (deqtype
                 (squash (sigma (pi a (univ (subst sh1 lv)))
                            (equal (fut (pi (subst sh1 a) (univ (subst (sh 2) lv)))) (subst sh1 y) (next (var 0)))))
                 (squash (sigma (pi a (univ (subst sh1 lv)))
                            (equal (fut (pi (subst sh1 a) (univ (subst (sh 2) lv)))) (subst sh1 y) (next (var 0))))))
    -> pseq G (deq y y (fut (pi a (univ (subst sh1 lv)))))
    -> pseq G (deq triv triv
                 (squash (sigma (pi a (univ (subst sh1 lv)))
                            (equal (fut (pi (subst sh1 a) (univ (subst (sh 2) lv)))) (subst sh1 y) (next (var 0)))))).
Proof.
intros G a lv y.
revert G.
refine (seq_pseq 1 [] lv 3 [] _ [] _ [] _ _ _); cbn.
intros G Hcllv Hseqa HseqC Hseqy.
rewrite -> seq_univ in Hseqa.
rewrite -> seq_eqtype in HseqC.
rewrite -> seq_deq in Hseqy |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (HseqC _#3 Hs) as (R & Hl & Hr & _ & _).
so (Hseqy _#3 Hs) as (F & Hfl & _ & Hm & _ & _).
so (Hseqa _#3 Hs) as (gpga & RA & Hlva & _ & HRA & _).
clear HseqC Hseqy Hseqa.
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
intros P B2 HP HB2 HeqB.
assert (exists T (HT : rel (den P) i T T),
          rel (den F) i (subst s y) (next T)
          /\ rel (den F) i (next T) (next T)) as (T & HT & HmT & HTT).
  {
  clear Hact Hsig HeqB HB2 Hl Hr HB HA.
  so (subst_closub _#4 Hcls Hcllv) as Hcllv'.
  invert (basic_value_inv _#6 value_pi HP).
  intros A Bp HA HBp <-.
  assert (forall j n n' Hn, pi1 Bp (urelspinj (den A) j n n' Hn) = iuuniv the_system j gpga) as HBpc.
    {
    intros j n n' Hn.
    assert (j <= i) as Hj.
      {
      so (basic_impl_iutruncate _#6 HA) as HeqA.
      assert (rel (den A) j n n') as Hn' by exact Hn.
      rewrite -> HeqA in Hn'.
      destruct Hn' as (Hj & _).
      omega.
      }
    invert HBp.
    intros _ _ HactP.
    so (HactP j n n' Hj Hn) as H.
    simpsubin H.
    invert (basic_value_inv _#6 value_univ H).
    intros gpg' Hlv' _ _ Heq.
    so (pginterp_fun _#3 Hlva Hlv'); subst gpg'.
    symmetry; exact Heq.
    }
  destruct i as [| k].
    {
    invert (basic_value_inv _#6 value_fut Hfl).
    intros _ <-.
    cbn in Hm.
    destruct Hm as (y0 & _ & _ & Hcly & _ & Hstepy & _ & _).
    assert (rel (den (iupi stop 0 A Bp)) 0 (lam unittp) (lam unittp)) as HT.
      {
      cbn.
      exists unittp, unittp.
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros j n n' Hj Hn.
      rewrite -> HBpc.
      cbn.
      split; [omega |].
      exists (iubase (unit_urel stop j)).
      rewrite -> sint_unroll.
      simpsub.
      split; apply interp_eval_refl; apply interp_unit.
      }
    exists (lam unittp), HT.
    split.
      {
      cbn.
      exists y0, (lam unittp).
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }

      {
      cbn.
      exists (lam unittp), (lam unittp).
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }
    }
  invert (basic_value_inv _#6 value_fut Hfl).
  intros Pk HPk <-.
  invert (basic_value_inv _#6 value_pi HPk).
  intros Ak Bk HAk HBk <-.
  so (interp_increase _#6 (toppg_max gpga) HRA) as HRA'.
  so (basic_fun _#7 HA HRA'); subst RA.
  so (interp_level_internal _#5 (cin_stop gpga) HRA) as (X & ->).
  so (basic_downward _#7 (Nat.le_succ_diag_r k) HA) as HAk'.
  so (basic_fun _#7 HAk HAk') as HeqAk.
  rewrite -> iutruncate_extend_iurel in HeqAk.
  subst Ak.
  assert (forall j n n' Hn, pi1 Bk (urelspinj _ j n n' Hn) = iuuniv the_system j gpga) as HBkc.
    {
    intros j n n' Hn.
    assert (j <= k) as Hj.
      {
      destruct Hn as (Hj & _).
      omega.
      }
    invert HBk.
    intros _ _ HactK.
    so (HactK j n n' Hj Hn) as H.
    simpsubin H.
    invert (basic_value_inv _#6 value_univ H).
    intros gpg' Hlv' _ _ Heq.
    so (pginterp_fun _#3 Hlva Hlv'); subst gpg'.
    symmetry; exact Heq.
    }
  cbn in Hm.
  destruct Hm as (y0 & y0' & _ & Hcly & _ & Hstepy & _ & Hrely).
  exploit Hrely as Hy0; [omega |].
  clear Hrely.
  so (arrow_univ_witness gpga (subst s lv) k X Bp Bk y0 y0' Hlva Hcllv' HBpc HBkc Hy0)
    as (T & HT & Hy0T & HTk).
  so (urel_closed _#5 HT) as (HclT & _).
  exists T, HT.
  split.
    {
    cbn.
    exists y0, T.
    do2 5 split; auto using star_refl; try prove_hygiene.
    }

    {
    cbn.
    exists T, T.
    do2 5 split; auto using star_refl; try prove_hygiene.
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
    replace X with (iusigma stop P B2) by exact HeqB
end.
cbn.
exists T, T, triv, triv, HT.
so (urel_closed _#5 HT) as (HclT & _).
do2 4 split; auto using star_refl; try prove_hygiene.
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iuequal stop true i F (subst s y) (next T) p q Hmp Hnq) by exact HeqB2
end.
cbn.
do2 5 split; auto using star_refl; try prove_hygiene.
Qed.
