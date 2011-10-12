Set Printing Universes.
Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories orders.maps interfaces.orders orders.orders
  interfaces.functors.
Require setoids.

Inductive Object := object { T:> Type; e: Equiv T; le: Le T; setoid_proof: Setoid T;  po_proof: PartialOrder le }.

Existing Instance e.
Existing Instance le.
Existing Instance setoid_proof.
Existing Instance po_proof.

Section contents.
  Global Instance Arrow: Arrows Object := λ A B, sig (@OrderPreserving A B _ _ _ _).

  Global Program Instance: ∀ x y: Object, Equiv (x ⟶ y) := λ _ _, respectful (=) (=).

  Existing Instance order_morphism_mor.
  Global Instance: ∀ x y: Object, Setoid (x ⟶ y).
  Proof with intuition.
   intros x y.
   constructor.
     intros [? ?] ? ? E. now rewrite E.
    intros ? ? E ? ? ?. symmetry...
   intros [f Pf] [g Pg] [h Ph] E1 E2 a b E3. simpl.
   transitivity (g a)...
  Qed.

  Global Program Instance: CatId Object := λ _, id.

  Local Obligation Tactic := idtac.
  Global Program Instance: CatComp Object := λ _ _ _, compose.
  Next Obligation. intros ? ? ? [? ?] [? ?]. apply _. Qed.

  Instance: ∀ x y z: Object, Proper ((=) ==> (=) ==> (=)) (comp x y z).
  Proof. repeat intro. simpl. firstorder. Qed.

  Global Instance: Category Object.
  Proof.
   constructor; try apply _.
     intros ? ? ? ? [??] [??] [??] ? ? E. simpl. now rewrite E.
    intros ? ? [??] ? ? E. simpl. now rewrite E.
   intros ? ? [??] ? ? E. simpl. now rewrite E.
  Qed.

  Definition forget (O: Object) : setoids.Object := setoids.object O _ _.
  Global Program Instance: Fmap forget := λ x y f, f.
  Next Obligation.
    constructor; try typeclasses eauto.
    destruct f.
    intros ???.
    simpl.
    rewrite H.
    reflexivity.
  Qed.

  Global Instance: Functor forget _ := {}.
  Proof.
    * constructor; try typeclasses eauto.
      intros ???. assumption.
    * intros ????. assumption.
    * intros ??[] ?[] ???.
    simpl. rewrite H.
    reflexivity.
  Qed.
End contents.
Implicit Arguments object [[e] [le] [setoid_proof] [po_proof]].
