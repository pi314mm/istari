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


(* Soundness of the rule futureArrowUnivSurj:

     G |- {exists (x : A -> univ I) . M = next x : future (A -> univ I)}
     >>
     G |- A : univ I
     G |- {exists (x : A -> univ I) . M = next x : future (A -> univ I)} : type
     G |- M : future (A -> univ I)

   This generalizes futureUnivSurj (SoundFutUniv.v) from univ I to
   A -> univ I.

   Notation used in the comments below:

     m ~ n in R @ i    means   rel (den R) i m n
     a => R            means   the term a is interpreted as the semantic
                               type R (interp/basic/sint)
     U_j               means   iuuniv the_system j gpg, the universe at
                               page gpg (the page lv denotes) at stage j
     l[n]              means   subst1 n l
     cut n R           means   iutruncate n R, R cut off at stage n
     w                 is      cin gpg, the level at which types in U
                               are interpreted

   In the universe case the witness was a semantic constant for a single
   type.  Here the witness is a function, so it is built from a semantic
   constant for a family of types:

     T  =  lam (con lv (ctapp Q (var 0)))

   where Q (see famobj) is the semantic constant for a family G over A's
   interpretation X, so that T n is the type G(n).  The work is in
   building G from the function y0 that y evaluates to (y = next y0):

     - extract_functional reads off the family Bf of types that y0's
       body produces on A at stages up to k;
     - make_family turns Bf into a family G at level w on all of X, by
       sending arguments above stage k to their stage k part;
     - ctapp_famobj computes what ctapp Q n means.

   arrow_univ_witness puts these together, and sound_fut_arrow_univ_surj
   follows the same outline as sound_fut_univ_surj. *)


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


(* A semantic constant for a family of types over D, at level w.
   It is an ext constant of kind qtarrow w D (qtype w), the kind of type
   families over D at level w, whose value is G. *)
Definition famobj w (D : wurel w) (G : urelsp D -n> wiurel_ofe w)
  (h : level (qtarrow w D (qtype w)) << stop) : sterm :=
  ext (objin (objsome (expair (qtarrow w D (qtype w)) G) h)).


(* What applying famobj means: if m (moved to level w) is the
   left or right side of a pair n ~ p in D @ j, then ctapp (famobj G) m
   is interpreted at stage j as the constructor G (n, p) cut off at stage
   S j. *)
Lemma ctapp_famobj :
  forall pg w (D : wurel w) (G : urelsp D -n> wiurel_ofe w) (h : level (qtarrow w D (qtype w)) << stop) (s : bool) j (m : sterm) (n p : wterm w) (Hnp : rel D j n p),
    w <<= cin pg
    -> map_term (extend stop w) m = (if s then n else p)
    -> cbasic the_system pg s j (ctapp (famobj w D G h) m)
         (expair (qtype w) (iutruncate (S j) (pi1 G (urelspinj D j n p Hnp)))).
Proof.
intros pg w D G h s j m n p Hnp Hw Hm.
(* At stage j, the constant famobj G means G standardized and projected
   to stage j, whose domain is D cut off at stage S j (ceiling (S j) D).
   The pair (n, p) is in that domain, since j < S j. *)
set (Hnp' := conj (Nat.lt_succ_diag_r j) Hnp : rel (ceiling (S j) D) j n p).
(* First rewrite the target into the form that interp_ctapp produces:
   the projected family applied to (n, p).  The replace leaves two goals:
   the interpretation in the rewritten form (handled first), and the
   equation itself (handled second). *)
replace (iutruncate (S j) (pi1 G (urelspinj D j n p Hnp)))
  with (pi1 (proj j (qtarrow w D (qtype w)) (std (S j) (qtarrow w D (qtype w)) G))
          (urelspinj (ceiling (S j) D) j n p Hnp')).
  {
  (* interp_ctapp: ctapp b m means the family b means, applied to (n, p).
     interp_ext: the ext constant means its value standardized and
     projected; its side condition is level (qtarrow w D (qtype w)) <<=
     cin pg, and that level is max w w = w. *)
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
(* The equation.  Projecting a family to stage j precomposes it with the
   embedding of ceiling (S j) D into D, which sends the class of (n, p) to
   the class of (n, p) in D (embed_ceiling_urelspinj).  Standardizing at
   S j cuts the result at stage min (S j) (S j') where j' is the stage of
   the argument, here j; so the cut is at S j. *)
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
(* F is the composite: cut C down to stage k, move it up to the top level,
   then apply Bf.  F is a family of top-level types over D; we want the
   level w types that its values come from. *)
set (F := nearrow_compose Bf
            (nearrow_compose (extend_urelsp_ne h (ceiling (S k) D))
               (proj_ceiling_ne (S k) (Nat.lt_0_succ k) D))).
(* Each F C is extend R0 for a unique R0: one exists by Hext, and it is
   unique because extend_iurel is injective. *)
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
(* Unique choice gives the function g with F C = extend (g C). *)
so (choice _#3 Huniq) as (g & Hg).
(* g is nonexpansive: F is, and extend_iurel does not shrink distances
   (it is noncontractive), so distances between values of g are no larger
   than between the corresponding values of F. *)
assert (@nonexpansive (urelsp D) (wiurel_ofe w) g) as Hne.
  {
  intros n C C' Hdist.
  apply (extend_iurel_noncontractive _ _ h).
  rewrite <- !Hg.
  apply (pi2 F).
  exact Hdist.
  }
(* So g is the family we want. *)
exists (expair g Hne).
intro C.
cbn.
rewrite <- Hg.
reflexivity.
Qed.


(* famobj is a closed constant: substitution leaves it alone, and it is
   closed. *)
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
(* y0 and y0' evaluate to lam l and lam l', and for every j <= k and
   n ~ n' in the domain at stage j, l[n] ~ l'[n'] in U_j @ j (Hact). *)
cbn in Hy0.
destruct Hy0 as (l & l' & _ & Hcly0 & Hcly0' & Hstep & Hstep' & Hact).
(* The bodies l and l' are closed apart from the bound variable, since
   y0 and y0' are closed and evaluation preserves closedness. *)
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
(* Ak is the domain at stage k: A's interpretation cut off at stage S k.
   Since it is already cut off, cutting it off at S k again changes
   nothing. *)
set (Ak := extend_iurel h (iutruncate (S k) X)).
assert (den Ak = ceiling (S k) (den Ak)) as HeqAk.
  {
  apply urel_extensionality.
  fextensionality 3.
  intros j m p.
  cbn.
  pextensionality; [intros (Hj & H); split; auto; omega | tauto].
  }
(* Read off the family of types that y0's body produces.  For each
   n ~ n' in Ak @ j, l[n] and l'[n'] are interpreted as the same type
   (that is what l[n] ~ l'[n'] in U_j means).  extract_functional
   collects these into a nonexpansive family Bf over Ak, so that
   (Hbf) l[n] => Bf (n, n') for every n ~ n' in Ak @ j with j <= k. *)
exploit (extract_functional gpg k (den Ak) l l') as (Bf & Hbf & _); auto.
  {
  intros j m p Hmp.
  (* Elements of Ak exist only at stages j <= k. *)
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
(* Each Bf C is a type in a universe at page gpg, so it is extended from
   level w (interp_level_internal). *)
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
(* Build G, a level w family on all of X (not just stages up to k), with
   (HG) extend (G C) = Bf (C cut down to stage k). *)
so (make_family w h k (den X) Bf Hext) as (G & HG).
(* The level of the kind qtarrow w (den X) (qtype w) is w, which is
   strictly below stop.  So G can be made into a semantic constant. *)
assert (level (qtarrow w (den X) (qtype w)) << stop) as hq.
  {
  cbn.
  rewrite -> max_ord_id.
  exact (le_lt_ord_trans _#3 (cin_top gpg) (succ_increase top)).
  }
(* The witness is T = lam body, where body = con lv (ctapp Q (var 0))
   applies the semantic constant Q for G to the bound variable, and
   turns the resulting constructor into a type in univ lv. *)
set (Q := famobj w (den X) G hq).
set (body := con lv (ctapp Q (var 0))).
(* Substituting into body touches only the variable, since lv and Q are
   closed. *)
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
(* What the body means (on either side b): if n ~ n' in X @ j (after
   moving n, n' to level w), then con lv (ctapp Q n) is interpreted at
   stage j as G (n, n') cut off at stage S j.  This combines interp_con
   with ctapp_famobj. *)
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
(* From here on only the facts above about body and Q are needed, not
   their definitions. *)
clearbody body Q.
(* T is in every arrow type D' -> U whose domain D' is contained in X
   and whose codomain family B' is the constant universe.  For
   n ~ n' in D' @ j, body[n] and body[n'] are both interpreted as
   G (n, n') cut off at stage S j (Hcon), so body[n] ~ body[n'] in U_j. *)
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
  (* T ~ T in the arrow type at stage S k, whose domain is extend X.
     Membership in extend X is membership in X after moving to level w,
     so the domain condition of HTT holds directly. *)
  apply HTT; auto.
  }

  {
  (* y0 ~ T in the arrow type at stage k.  y0 evaluates to lam l and T is
     already lam body.  For j <= k and n ~ n' in Ak @ j, we need
     l[n] ~ body[n'] in U_j @ j: both sides must be interpreted as the
     same type.  On the left, l[n] => Bf (n, n') (Hbf). *)
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
  (* On the right, body[n'] => G (n, n') cut off at stage S j (Hcon).  It
     remains to show that this is Bf (n, n').  Membership in Ak is a stage
     bound j < S k together with membership in X, so proj2 Hn gives
     n ~ n' in X. *)
  rewrite -> Hbody.
  replace (pi1 Bf (urelspinj (den Ak) j n n' Hn))
    with (extend_iurel h (iutruncate (S j) (pi1 G (urelspinj (den X) j _ _ (proj2 Hn))))).
    {
    exact (Hcon false j n n' (proj2 Hn)).
    }
  (* The calculation:
       extend (cut (S j) (G C))
     = cut (S j) (extend (G C))                       iutruncate_extend_iurel
     = cut (S j) (Bf (C cut down to stage k))         HG
     = cut (S j) (Bf (n, n'))                         Heqc, below
     = Bf (n, n')                                     basic_impl_iutruncate
     where C is the class of (n, n') in X. *)
  rewrite <- iutruncate_extend_iurel.
  rewrite -> HG.
  (* Heqc: the class of (n, n') in X, cut down to stage k and moved to the
     top level, is the class of (n, n') in Ak.  Both are sets of pairs
     (i', z); the two predicates differ only in the order of the stage
     bounds i' < S k and i' <= j. *)
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
  (* Bf (n, n') is an interpretation at stage j, so it is already cut off
     at stage S j. *)
  symmetry.
  exact (basic_impl_iutruncate _#6 (Hfun j n n' Hj Hn)).
  }

  {
  (* T ~ T in the arrow type at stage k, whose domain is Ak.  Membership in
     Ak implies membership in X (drop the stage bound). *)
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
(* Change pseq to seq.  There is one hygiene premise (lv is well-scoped
   in G, giving Hcllv) and three judgement premises. *)
refine (seq_pseq 1 [] lv 3 [] _ [] _ [] _ _ _); cbn.
intros G Hcllv Hseqa HseqC Hseqy.
(* Unfold the judgements: Hseqa says a : univ lv, HseqC says the squashed
   sigma type (call it C) is a type, Hseqy says y : fut (a -> univ lv),
   and the goal is triv : C. *)
rewrite -> seq_univ in Hseqa.
rewrite -> seq_eqtype in HseqC.
rewrite -> seq_deq in Hseqy |- *.
(* Fix a stage i and substitutions s, s' that are related at stage i. *)
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
(* R interprets C, F interprets fut (a -> univ lv) and y[s] ~ y[s'] in F
   @ i (Hm), and lv[s] denotes the page gpga, at which a[s] => RA. *)
so (HseqC _#3 Hs) as (R & Hl & Hr & _ & _).
so (Hseqy _#3 Hs) as (F & Hfl & _ & Hm & _ & _).
so (Hseqa _#3 Hs) as (gpga & RA & Hlva & _ & HRA & _).
clear HseqC Hseqy Hseqa.
(* Use R as the interpretation of C; it remains to show
   triv ~ triv in R @ i. *)
exists R.
cut (rel (den R) i triv triv).
  {
  intro H.
  do2 4 split; auto; simpsub; auto.
  }
(* Take R apart, exactly as in sound_fut_univ_surj: squash is a set over
   unit, and the fiber at triv is the sigma type, whose first component
   a -> univ lv is interpreted as P. *)
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
(* The main step: find T in P such that y = next T in F at stage i, i.e.,
     y[s] ~ next T in F @ i   and   next T ~ next T in F @ i. *)
assert (exists T (HT : rel (den P) i T T),
          rel (den F) i (subst s y) (next T)
          /\ rel (den F) i (next T) (next T)) as (T & HT & HmT & HTT).
  {
  clear Hact Hsig HeqB HB2 Hl Hr HB HA.
  so (subst_closub _#4 Hcls Hcllv) as Hcllv'.
  (* P = iupi stop i A Bp, where a => A and Bp is the codomain family. *)
  invert (basic_value_inv _#6 value_pi HP).
  intros A Bp HA HBp <-.
  (* The codomain family Bp is constantly the universe: at any
     n ~ n' in A @ j it is U_j at page gpga.  (The universe term denotes
     gpga by Hlva, and pages are unique by pginterp_fun.) *)
  assert (forall j n n' Hn, pi1 Bp (urelspinj (den A) j n n' Hn) = iuuniv the_system j gpga) as HBpc.
    {
    intros j n n' Hn.
    (* A is an interpretation at stage i, so it is cut off at stage S i,
       and elements of A exist only at stages j <= i. *)
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
    (* Stage 0.  As in the universe case, fut at stage 0 requires nothing
       beneath next, so any element of P works; we use lam unittp, the
       function that always returns unit. *)
    invert (basic_value_inv _#6 value_fut Hfl).
    intros _ <-.
    cbn in Hm.
    (* y[s] evaluates to next y0. *)
    destruct Hm as (y0 & _ & _ & Hcly & _ & Hstepy & _ & _).
    (* lam unittp is in P at stage 0: for n ~ n' in A @ j, unittp ~ unittp
       in U_j, since both sides interpret unittp as unit. *)
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
      (* y[s] ~ next (lam unittp): both evaluate to next of something, and
         nothing more is required at stage 0. *)
      cbn.
      exists y0, (lam unittp).
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }

      {
      (* next (lam unittp) ~ next (lam unittp), likewise. *)
      cbn.
      exists (lam unittp), (lam unittp).
      do2 5 split; auto using star_refl; try prove_hygiene.
      intros; omega.
      }
    }
  (* Stage S k.  F is fut (S k) of Pk, the interpretation of a -> univ lv
     at stage k, and Pk = iupi stop k Ak Bk where a => Ak at stage k. *)
  invert (basic_value_inv _#6 value_fut Hfl).
  intros Pk HPk <-.
  invert (basic_value_inv _#6 value_pi HPk).
  intros Ak Bk HAk HBk <-.
  (* Relate the interpretations of a.  The premise a : univ lv gives
     a => RA at page gpga; that also holds at the top page
     (interp_increase), so RA = A by uniqueness of interpretations. *)
  so (interp_increase _#6 (toppg_max gpga) HRA) as HRA'.
  so (basic_fun _#7 HA HRA'); subst RA.
  (* Since a is in the universe at page gpga, A comes from level cin gpga:
     A = extend X. *)
  so (interp_level_internal _#5 (cin_stop gpga) HRA) as (X & ->).
  (* At stage k, a means A cut off at stage S k (basic_downward), so
     Ak = cut (S k) (extend X) = extend (cut (S k) X). *)
  so (basic_downward _#7 (Nat.le_succ_diag_r k) HA) as HAk'.
  so (basic_fun _#7 HAk HAk') as HeqAk.
  rewrite -> iutruncate_extend_iurel in HeqAk.
  subst Ak.
  (* The codomain family Bk at stage k is also constantly the universe at
     page gpga, by the same argument as HBpc.  Here j <= k comes directly
     from the stage bound in the cut-off domain. *)
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
  (* y[s] evaluates to next y0, and since S k > 0, y0 ~ y0' in Pk @ k:
     y0 is a function into the universe at stage k. *)
  cbn in Hm.
  destruct Hm as (y0 & y0' & _ & Hcly & _ & Hstepy & _ & Hrely).
  exploit Hrely as Hy0; [omega |].
  clear Hrely.
  (* The witness T, from arrow_univ_witness: it is in P at stage S k, and
     y0 ~ T and T ~ T in Pk at stage k. *)
  so (arrow_univ_witness gpga (subst s lv) k X Bp Bk y0 y0' Hlva Hcllv' HBpc HBkc Hy0)
    as (T & HT & Hy0T & HTk).
  so (urel_closed _#5 HT) as (HclT & _).
  exists T, HT.
  split.
    {
    (* y[s] ~ next T in fut (S k) Pk: y[s] evaluates to next y0, next T is
       a value, and y0 ~ T in Pk @ k (Hy0T). *)
    cbn.
    exists y0, T.
    do2 5 split; auto using star_refl; try prove_hygiene.
    }

    {
    (* next T ~ next T in fut (S k) Pk: T ~ T in Pk @ k (HTk). *)
    cbn.
    exists T, T.
    do2 5 split; auto using star_refl; try prove_hygiene.
    }
  }
(* Build the inhabitant, as in sound_fut_univ_surj.  The fiber of B2 at T
   is the equality type equal (fut (a -> univ lv)) y (next T), whose
   underlying type is interpreted as F. *)
invert HB2.
intros _ _ Hact2.
so (Hact2 i T T (le_refl _) HT) as Heq.
simpsubin Heq.
invert (basic_value_inv _#6 value_equal Heq).
intros p q A Hmp Hnq HA' HeqB2.
so (basic_fun _#7 HA' Hfl); subst A.
(* triv ~ triv in the set type: triv is in unit, and the set's predicate
   is inhabited by the pair <T, triv>. *)
cbn.
exists (ppair T triv), (ppair T triv), Htriv.
cbn.
(* Replace the fiber of B at triv by the sigma type (HeqB). *)
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iusigma stop P B2) by exact HeqB
end.
cbn.
(* <T, triv> ~ <T, triv> in the sigma: T ~ T in P (HT), and it remains to
   show triv ~ triv in the fiber of B2 at T. *)
exists T, T, triv, triv, HT.
so (urel_closed _#5 HT) as (HclT & _).
do2 4 split; auto using star_refl; try prove_hygiene.
(* Replace the fiber of B2 at T by the equality type (HeqB2).  triv ~ triv
   there holds because y[s] and next T are both related to next T in F
   (HmT and HTT). *)
match goal with
| |- rel (den ?X) _ _ _ =>
    replace X with (iuequal stop true i F (subst s y) (next T) p q Hmp Hnq) by exact HeqB2
end.
cbn.
do2 5 split; auto using star_refl; try prove_hygiene.
Qed.
