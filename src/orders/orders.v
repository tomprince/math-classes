Require Import Morphisms Setoid Program abstract_algebra.

Section contents.
  Context `{Setoid A} `{Order A}.

  Lemma strictly_precedes_weaken x y : x < y → x ≤ y.
  Proof. firstorder. Qed.

  Lemma precedes_flip {t : TotalOrder (≤)} x y : ¬y ≤ x → x ≤ y.
  Proof. firstorder. Qed.

  Lemma neq_precedes_precedes x y : (x ≠ y ∧ x ≤ y) ↔ x < y.
  Proof. firstorder. Qed.

  Lemma strictly_precedes_flip {t : TotalOrder (≤)} x y : ¬y < x → y ≠ x → x < y.
  Proof. firstorder. Qed.

  Lemma equiv_not_strictly_precedes x y : x = y → ¬x < y.
  Proof. firstorder. Qed.

  Context `{!Proper ((=) ==> (=) ==> iff) (≤)}.

  Global Instance: Proper ((=) ==> (=) ==> iff) (<).
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    unfold "<". rewrite E1, E2. tauto.
  Qed.

  Global Instance strickly_precedes_trans {t : Transitive (≤)} {a : AntiSymmetric (≤)} : 
    Transitive (<).
  Proof with auto.
    intros x y z E1 E2.
    destruct E1 as [E1a E1b]. destruct E2 as [E2a E2b].
    split. transitivity y...
    intro E. rewrite E in E1a. eapply E2b.  
    apply (antisymmetry (≤))...
  Qed.

  Lemma equiv_precedes {r : Reflexive (≤)} x y : x = y → x ≤ y.
  Proof. 
    intros E. rewrite E. reflexivity.
  Qed.

  Lemma equal_strictly_precedes_precedes {r : Reflexive (≤)} x y : (x = y ∨ x < y) → x ≤ y.
  Proof with auto.
    intros [E|E]. apply equiv_precedes... firstorder.
  Qed.

  Lemma strictly_precedes_precedes x y {r : Reflexive (≤)} `{∀ x y, Decision (x = y)} : (x = y ∨ x < y) ↔ x ≤ y.
  Proof with auto.
    split.
    apply equal_strictly_precedes_precedes.
    intros E. destruct (decide (x = y))... right; split...
  Qed.

  Lemma not_precedes_strictly_precedes {t : TotalOrder (≤)} {r : Reflexive (≤)} {a : AntiSymmetric (≤)}
    x y : ¬y ≤ x ↔ x < y.
  Proof with auto.
    split. 
    intros E. split. apply precedes_flip... 
    intros F. apply E. apply equiv_precedes. symmetry...
    firstorder.
  Qed.

  Lemma not_strictly_precedes_precedes {t : TotalOrder (≤)} {r : Reflexive (≤)} {a : AntiSymmetric (≤)} `{∀ x y, Decision (x ≤ y)}
    x y : ¬y < x ↔ x ≤ y.
  Proof with auto.
    split; intros E. 
    apply stable. intros F. apply E, not_precedes_strictly_precedes...
    firstorder. 
  Qed.

  Lemma precedes_or_strictly_precedes {t : TotalOrder (≤)} {r : Reflexive (≤)} `{∀ x y, Decision (x ≤ y)} x y : 
    x ≤ y ∨ y < x.
  Proof with auto. 
    destruct (decide (x ≤ y)) as [|E]...
    right. split. apply precedes_flip...
    intro. apply E. apply equiv_precedes. symmetry...
  Qed.

  Lemma strictly_precedes_or_equiv {t : TotalOrder (≤)} {r : Reflexive (≤)} `{∀ x y, Decision (x ≤ y)} `{∀ x y, Decision (x = y)} x y : 
    x < y ∨ x = y ∨ y < x.
  Proof.
    destruct (precedes_or_strictly_precedes x y) as [E|E].
    apply strictly_precedes_precedes in E; try apply _.
    intuition. intuition.
  Qed.

  Global Instance strictly_precedes_dec_slow `{∀ x y, Decision (x ≤ y)} `{∀ x y, Decision (x = y)} : 
    ∀ x y, Decision (x < y) | 10.
  Proof with auto.
    intros x y.
    destruct (decide (x ≤ y)) as [|E].
    destruct (decide (x = y)).
    right. apply equiv_not_strictly_precedes...
    left; split...
    right. intros F. apply E. apply strictly_precedes_weaken...
  Qed.

  Global Instance strictly_precedes_dec {t : TotalOrder (≤)} {r : Reflexive (≤)} {a : AntiSymmetric (≤)} `{∀ x y, Decision (x ≤ y)} : 
    ∀ x y, Decision (x < y) | 9.
  Proof with auto.
    intros x y.
    destruct (decide (y ≤ x)).
    right. intro. apply (not_precedes_strictly_precedes x y)...
    left. apply not_precedes_strictly_precedes...
  Qed.
End contents.