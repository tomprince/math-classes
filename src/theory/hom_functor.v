Require Import
  Relation_Definitions
  abstract_algebra theory.setoids interfaces.functors theory.categories.

Require categories.setoids categories.dual.
Require Import workaround_tactics.

Section contents.

  Context `{Category C} (x: C).

  Definition homFrom (y: C): setoids.Object := @setoids.object (x ⟶ y) _ _.

  Global Program Instance: Fmap homFrom := λ v w X, (X ◎): (x ⟶ v) → (x ⟶ w).
  Next Obligation. constructor; apply _. Qed.

  Global Instance: Functor homFrom _.
  Proof.
   constructor; try apply _.
     constructor; try apply _.
     repeat intro. simpl in *.
     apply comp_proper; auto.
    repeat intro.
    simpl.
    rewrite H1.
    apply left_identity.
   repeat intro.
   simpl.
   unfold compose.
   rewrite H1.
   symmetry.
   apply comp_assoc.
  Qed.

  Context `{!Functor (F:C -> setoids.Object) F'}.
  Definition Nat := {η : homFrom ⇛ F | NaturalTransformation η}.
  Instance: ∀ v w, Proper ((=) ==> (=)) (fmap F (v:=v)(w:=w)).
    repeat intro.
    (* FIXME *)
    apply Functor0; [try rewrite H1; reflexivity| assumption].
  Qed.
  Program Definition l : Nat → setoids.T (F x) := λ X, ` (X x) cat_id.
  Program Instance r: Inverse l (* setoid.T (F x) → Nat homFrom ⇛ F*) := λ X a t, ` (F' _ _ t) X.
  Next Obligation.
    constructor; try typeclasses eauto.
    intros A B ?.
    simpl in *.
    apply Functor0; [rewrite H1|]; reflexivity.
  Qed.
  Next Obligation.
    intros a b f s t Hst. simpl.
    fold (fmap (v:=x)(w:=b) F).
    fold (fmap (v:=x)(w:=a) F).
    unfold compose.
    pose (preserves_comp F f s X X (reflexivity _)) as e.
    rewrite e; clear e.
    simpl; unfold compose.
    simpl in *.
    pose (functor_morphism F a b).
    apply s0.
    apply Proper_instance_0; [assumption|reflexivity].
  Qed.

  Global Instance: Equiv (homFrom  ⇛ F) := pointwise_dependent_relation C (λ a, homFrom a ⟶ F a) (λ a, (=)).
  Global Instance: Equiv Nat  := sig_equiv (H:=Equiv_instance_0) _.
  Global Instance sm_l: Setoid_Morphism l.
  Proof.
    constructor; try typeclasses eauto.
    repeat intro.
    apply H1.
    reflexivity.
  Qed.
  Global Instance: Surjective l.
  Proof.
    constructor; try apply _.
    unfold l, inverse, r.
    intros a ??.
    rewrite (preserves_id F x a); simpl; [reflexivity|assumption].
  Qed.
  Hint Extern 1 (Proper _ (proj1_sig ?x)) => apply (@sm_proper _ _ _ _ _ (proj2_sig x)) : typeclass_instances.

  Global Instance: Injective l.
    constructor; try apply _.
    intros [? Na] [? Nb] ? ? u v ?.
    simpl in *.
    rewrite <-(right_identity u).
    rewrite <-(right_identity v).
    posed_rewrite (Na _ _ u cat_id cat_id (reflexivity _)).
    posed_rewrite (Nb _ _ v cat_id cat_id (reflexivity _)).
    simpl.
    apply (proper_prf (m:=fmap F) u v); auto.
  Qed.
  Global Instance: Bijective l := {}.

End contents.

Notation homTo := (homFrom (Arrows0:=flip (_: Arrows _))).
