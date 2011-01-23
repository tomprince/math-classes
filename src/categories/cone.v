Require Import
    Morphisms RelationClasses Equivalence Setoid
    abstract_algebra interfaces.functors
    extra_tactics.

Section Cone.
Context `(Category J) `(Category C) `{!Functor (X:J->C) X'}.

Class Cone (c:C) (f:forall j:J, c ⟶ X j) := cone :
  forall (j j': J) (a:j⟶j'), (fmap X a) ◎ f j = f j'.

Class ConeMorphism `(Cone c f) `(Cone c' f') (mu: c ⟶ c') := cone_morphism :
  forall j:J, f' j ◎ mu = f j.

Record Object := object {
  vertex :> C;
  legs :> forall j:J, vertex ⟶ X j;
  cone_instance :> Cone vertex legs
}.

Record Arrow (x y: Object) : Type := arrow {
  morphism :> vertex x ⟶ vertex y;
  cone_morphism_instance :> ConeMorphism x y morphism
}.
Implicit Arguments arrow [[x] [y]].
Implicit Arguments morphism [[x] [y]].

Global Instance: Arrows Object := Arrow.
Hint Extern 4 (Arrows Object) => exact Arrow: typclasses_instance.

Section contents.
Section more_arrows. Context (x y: Object).
    Global Instance e: Equiv (x ⟶ y) := fun f g => morphism f = morphism g.

    Let e_refl: Reflexive e.
    Proof.
      intro; unfold e; reflexivity.
    Qed.

    Let e_sym: Symmetric e.
    Proof.
      intros ??; unfold e; symmetry; trivial.
    Qed.

    Let e_trans: Transitive e.
    Proof. intros ???; unfold e; intros ??; do 2 hyp_rewrite; reflexivity. Qed.
    Instance: Equivalence e.
    Global Instance: Setoid (x⟶y).
  End more_arrows.

    Global Program Instance: CatId Object := fun x => arrow cat_id _.
    Next Obligation.
      intros ?; apply right_identity.
    Qed.

    Global Program Instance: CatComp Object := fun x y z f g => arrow ((morphism f)◎ (morphism g)) _.
    Next Obligation.
      intro. rewrite comp_assoc. do 2 rewrite cone_morphism_instance. reflexivity.
    Qed.

    Global Instance: forall x y: Object, LeftIdentity (comp: _ → _ → x ⟶ y) cat_id.
    Proof.
      repeat intro.
      do 2 red; simpl.
      apply left_identity.
    Qed.
    Global Instance: forall x y: Object, RightIdentity (comp: _ → _ → x ⟶ y) cat_id.
    Proof.
      repeat intro.
      do 2 red; simpl.
      apply right_identity.
    Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      do 2 red; simpl.
      apply comp_assoc.
    Qed.
  End comp_assoc.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros ??? ??? ???.
    do 2 red.
    unfold comp.
    red; simpl.
    apply comp_proper; trivial.
  Qed.

  Global Instance: Category Object := { comp_assoc := comp_assoc' }.

End contents.

End Cone.
