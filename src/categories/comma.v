Require Import
    Morphisms RelationClasses Equivalence Setoid
    abstract_algebra interfaces.functors categories square
    extra_tactics.

Section Comma.
Context `{Category L} `{Category R} `{Category C}.
Context (F:L->C) `{!Functor (F:L->C) F_fmap} (G:R->C) `{!Functor (G:R->C) G_fmap}.

Record Object: Type := object {
  left_object : L;
  right_object : R;
  comma_map :> Comma F G left_object right_object
}.

Record Arrow (x y : Object) : Type := arrow {
  left_map : left_object x ⟶ left_object y;
  right_map : right_object x ⟶ right_object y;
  commutes :> Square (fmap F left_map) (fmap G right_map) (comma_map x) (comma_map y)
}.
Implicit Arguments left_map [[x] [y]].
Implicit Arguments right_map [[x] [y]].
Implicit Arguments arrow [[x] [y]].

Global Instance: Arrows Object := Arrow.
Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances.

Section contents.
  Section more_arrows. Context (x y: Object).
    Global Program Instance e: Equiv (x ⟶ y) := fun f g =>
      left_map f = left_map g /\ right_map f = right_map g.

    Instance: Equivalence e.
    Proof. prove_equivalence. Qed.
    Global Instance: Setoid (x ⟶ y).
  End more_arrows.

  (* Hint Extern 4 => rewrite preserves_id : typeclass_instances. *)
  Hint Extern 0 => match goal with | [ |- context [@fmap] ] => match goal with
                     | [ |- context [fmap _ cat_id] ] => rewrite preserves_id
                     | [ |- context [fmap _ (_ ◎ _)] ] => rewrite preserves_comp
                   end end : typeclass_instances.
  Hint Resolve @transpose_square : typeclass_instances.
  Global Program Instance: CatId Object := fun _ => arrow cat_id cat_id _.

  (* Time Global Instance: CatComp Object := fun _ _ _ f g => arrow (left_map f ◎ left_map g) (right_map f ◎ right_map g) _. *)
  Global Instance: CatComp Object.
  Proof.
    intros x y z f g.
    apply (arrow (left_map f◎left_map g) (right_map f ◎right_map g)).
    Time rewrite (preserves_comp F (left_map f) (left_map g)).
    Time rewrite preserves_comp; trivial.
    eapply @transpose_square; trivial.
    eapply @Square_instance_0; trivial; do 2 hyp_apply.
  Defined.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros.
    intros ? ? [? ?].
    intros ? ? [? ?].
    split; simpl; do 2 hyp_rewrite; reflexivity.
  Qed.

  Global Instance: forall x y: Object, LeftIdentity (comp: _ → _ → x ⟶ y) cat_id.
  Proof.
    split; simpl; apply left_identity.
  Qed.
  Global Instance: forall x y: Object, RightIdentity (comp: _ → _ → x ⟶ y) cat_id.
  Proof.
    split; simpl; apply right_identity.
  Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      split; simpl; apply comp_assoc.
    Qed.
  End comp_assoc.
  Global Instance: Category Object := { comp_assoc := comp_assoc' }.
End contents.

End Comma.
