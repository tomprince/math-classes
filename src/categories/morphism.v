Require Import
	Morphisms RelationClasses Equivalence Setoid
	abstract_algebra functors categories square
        extra_tactics.

Section MorCat.
Context `{Category A}.

Record Object: Type := object {
  initial: A;
  terminal: A;
  arr:> initial ⟶ terminal
}.

Implicit Arguments object [[initial] [terminal]].
Record Arrow (i p: Object) : Type := arrow {
  top : initial i ⟶ initial p;
  bottom : terminal i ⟶ terminal p;
  sqaure : Square (arr i) (arr p) top bottom
}.
Implicit Arguments top [[i] [p]].
Implicit Arguments bottom [[i] [p]].
Implicit Arguments arrow [[i] [p]].

Global Existing Instance sqaure.
Global Instance: Arrows Object := Arrow.

Section contents.
  Section more_arrows. Context (i p: Object).
    Global Program Instance e: Equiv (i ⟶ p) := fun sq sq' =>
      top sq = top sq' /\ bottom sq = bottom sq'.

    Instance: Equivalence e.
    Proof. prove_equivalence. Qed.
    Global Instance: Setoid (i⟶p).
  End more_arrows.

  Global Instance: CatId Object := fun _ => arrow cat_id cat_id _.
  Global Instance: CatComp Object := fun _ _ _ m n => arrow ((top m) ◎ top n) (bottom m ◎ bottom n) _.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros.
    intros ? ? [? ?].
    intros ? ? [? ?].
    split; simpl; do 2 hyp_rewrite; reflexivity.
  Qed.

  Global Instance: forall x y: Object, LeftIdentity (comp: _ → _ → x ⟶ y) cat_id.
  Proof. split; simpl; apply left_identity. Qed.

  Global Instance: forall x y: Object, RightIdentity (comp: _ → _ → x ⟶ y) cat_id.
  Proof. split; simpl; apply right_identity. Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof. split; simpl; apply comp_assoc. Qed.
  End comp_assoc.

  Global Instance: Category Object := { comp_assoc := comp_assoc' }.
End contents.
End MorCat.
Coercion object: canonical_names.Arrow >-> Object.
