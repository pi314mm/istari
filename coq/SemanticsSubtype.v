
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Dynamic.
Require Import Hygiene.
Require Import Equivalence.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import System.
Require Import MapTerm.
Require Import Extend.
Require Import Model.
Require Import Standard.
Require Import Truncate.
Require Import Equivalences.
Require Import Ceiling.
Require Import SemanticsProperty.


Definition subtype_property w (R R' : wurel w) : nat -> Prop
  :=
  fun j => 
    forall k m p,
      k <= j
      -> rel R k m p
      -> rel R' k m p.


Lemma subtype_property_downward :
  forall w R R' j,
    subtype_property w R R' (S j)
    -> subtype_property w R R' j.
Proof.
unfold subtype_property.
intros w R R' j Hsub.
intros k m p Hk Hmp.
apply Hsub; auto.
Qed.


Definition subtype_urel w i (R R' : wurel w) : wurel w :=
  property_urel (subtype_property w R R') w i (subtype_property_downward w R R').


Definition iusubtype w i (R R' : wiurel w) : wiurel w
  :=
  (subtype_urel w i (den R) (den R'),
   meta_pair
     (meta_iurel R)
     (meta_iurel R')).


Lemma iusubtype_inj :
  forall w i R1 R1' R2 R2',
    iusubtype w i R1 R2 = iusubtype w i R1' R2'
    -> R1 = R1' /\ R2 = R2'.
Proof.
intros w i R1 R1' R2 R2' Heq.
so (f_equal snd Heq) as Heq'.
cbn in Heq'.
so (meta_pair_inj _#5 Heq') as (Heq1 & Heq2).
split.
  {
  eapply meta_iurel_inj; eauto.
  }

  {
  eapply meta_iurel_inj; eauto.
  }
Qed.
