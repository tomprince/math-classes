Require Import
  Relation_Definitions abstract_algebra theory.categories interfaces.functors.

Section contents.
  Notation "C '^op'" := C (at level 1).

  Context `{c: @Category Object A Aeq Aid Acomp}.

  Global Instance flipA: Arrows Object^op := flip A.

  Global Instance: CatId Object^op := Aid.
  Global Instance: CatComp Object^op := λ _ _ _, flip (Acomp _ _ _).
  Global Instance e: ∀ x y: Object^op, Equiv (x ⟶ y) | 1000 := λ x y, Aeq y x.
  Local Existing Instance e.

  Global Instance: ∀ (x y: Object^op), Equivalence (e x y).
  Proof. intros. change (Equivalence ((=): Equiv (A y x))). apply _. Qed.

  Global Instance: ∀ (x y: Object^op), Setoid (x ⟶ y) := {}.

  Global Instance: ∀ (x y z: Object^op), Proper ((=) ==> (=) ==> (=)) (comp x y z).
  Proof.
   intros x y z ? ? E ? ? F.
   change (comp (H:=A) _ _ _ x1 x0 = comp (H:=A) _ _ _ y1 y0).
   now rewrite E, F.
  Qed.

  Instance cat: @Category Object^op flipA _ _ _.
  Proof with auto.
   destruct c.
   constructor; try apply _; auto.
     repeat intro. symmetry. apply comp_assoc.
    intros. apply id_r.
   intros. apply id_l.
  Qed.

End contents.
  Global Hint Cut [ !*; e; e ] : typeclass_instances.

Section functors.

  (** Given a functor F: C → D, we have a functor F^op: C^op → D^op *)

  Context {C D} F `{Functor C (H:=Ce) D (H1:=De) F}.

  Definition fmap_op: @Fmap C flipA D flipA F := fun v w => fmap F (v:=w)(w:=v).

  Global Instance: Functor F fmap_op.
  Proof with intuition.
    unfold e, fmap_op, flipA, flip, CatId_instance_0, CatComp_instance_0, flip.
    pose proof (functor_from F).
    pose proof (functor_to F).
    constructor; repeat intro.
    - apply cat.
    - apply cat.
    - constructor; typeclasses eauto.
    - set (preserves_id F a)...
    - set (preserves_comp F (H3:=H3) g f)...
  Qed.

End functors.
