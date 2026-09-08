import Definitions.Def_PvsNP
import Mathlib

open PvsNP

/-- Decode a `List Bool` (least-significant bit first, matching `Nat.bits`) back into a
natural number: the left inverse of `Nat.bits`. -/
private def decodeBits : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (decodeBits l)

private theorem decodeBits_bits (n : ℕ) : decodeBits (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp [decodeBits]
    · have hdecr : Nat.div2 n < n := Nat.binaryRec_decreasing hn
      have hside : Nat.div2 n = 0 → Nat.bodd n = true := by
        intro h0
        rw [Nat.div2_val] at h0
        have hn1 : n = 1 := by omega
        subst hn1
        rfl
      have hbits : Nat.bits n = Nat.bodd n :: Nat.bits (Nat.div2 n) := by
        conv_lhs => rw [← Nat.bit_bodd_div2 n]
        exact Nat.bits_append_bit _ _ hside
      rw [hbits, decodeBits, ih _ hdecr, Nat.bit_bodd_div2]

private theorem myBitsInjective : Function.Injective Nat.bits := by
  intro a b h
  have h' := congrArg decodeBits h
  rwa [decodeBits_bits, decodeBits_bits] at h'

/-- General self-delimiting-code lemma: if `f` maps every element to a nonempty code starting
with `false`, `f` is itself "injective up to a shared suffix", and `term` is a fixed marker
starting with `true` (so it cannot be confused with any `f a`), then flat-mapping `f` over a
list and appending `term` is injective up to a shared suffix. This is the combinatorial core
shared by both the literal-data blocks (`f = fun b => [false, b]`) and the clause-level
literal list (`f = encodeLiteral`). -/
private theorem flatMap_term_inj {α : Type} (f : α → List Bool) (term : List Bool)
    (hhead : ∀ a, ∃ r, f a = false :: r)
    (hterm : ∃ r, term = true :: r)
    (hinj : ∀ a1 a2 (s1 s2 : List Bool), f a1 ++ s1 = f a2 ++ s2 → a1 = a2 ∧ s1 = s2) :
    ∀ (L1 L2 : List α) (s1 s2 : List Bool),
      L1.flatMap f ++ (term ++ s1) = L2.flatMap f ++ (term ++ s2) → L1 = L2 ∧ s1 = s2 := by
  obtain ⟨rt, hterm⟩ := hterm
  intro L1
  induction L1 with
  | nil =>
    intro L2 s1 s2 heq
    cases L2 with
    | nil =>
      simp only [List.flatMap_nil, List.nil_append] at heq
      exact ⟨rfl, List.append_cancel_left heq⟩
    | cons a2 L2' =>
      exfalso
      obtain ⟨r2, hr2⟩ := hhead a2
      simp only [List.flatMap_nil, List.nil_append, List.flatMap_cons, hr2, hterm,
        List.cons_append, List.append_assoc] at heq
      injection heq with hb _
      exact Bool.noConfusion hb
  | cons a1 L1' ih =>
    intro L2 s1 s2 heq
    cases L2 with
    | nil =>
      exfalso
      obtain ⟨r1, hr1⟩ := hhead a1
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, hr1, hterm,
        List.cons_append, List.append_assoc] at heq
      injection heq with hb _
      exact Bool.noConfusion hb
    | cons a2 L2' =>
      simp only [List.flatMap_cons, List.append_assoc] at heq
      obtain ⟨ha, hrest⟩ := hinj a1 a2 _ _ heq
      obtain ⟨hL, hs⟩ := ih L2' s1 s2 hrest
      exact ⟨by rw [ha, hL], hs⟩

private theorem hinj_data :
    ∀ b1 b2 (s1 s2 : List Bool), ([false, b1] : List Bool) ++ s1 = [false, b2] ++ s2 →
      b1 = b2 ∧ s1 = s2 := by
  intro b1 b2 s1 s2 h
  simpa using h

private theorem data_flatMap_inj :
    ∀ (L1 L2 : List Bool) (s1 s2 : List Bool),
      L1.flatMap (fun b => [false, b]) ++ ([true, false] ++ s1) =
        L2.flatMap (fun b => [false, b]) ++ ([true, false] ++ s2) →
      L1 = L2 ∧ s1 = s2 :=
  flatMap_term_inj (fun b => [false, b]) [true, false]
    (fun a => ⟨[a], rfl⟩) ⟨[false], rfl⟩ hinj_data

private theorem encodeLiteral_inj_with_suffix (l1 l2 : Literal) (s1 s2 : List Bool)
    (h : encodeLiteral l1 ++ s1 = encodeLiteral l2 ++ s2) : l1 = l2 ∧ s1 = s2 := by
  unfold encodeLiteral at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hL, hs⟩ := data_flatMap_inj _ _ s1 s2 h
  injection hL with hsign hbits
  exact ⟨Prod.ext hsign (myBitsInjective hbits), hs⟩

private theorem encodeLiteral_head (l : Literal) : ∃ r, encodeLiteral l = false :: r :=
  ⟨l.1 :: ((Nat.bits l.2).flatMap (fun b => [false, b]) ++ [true, false]), by
    simp [encodeLiteral, List.flatMap_cons]⟩

private theorem clause_flatMap_inj :
    ∀ (L1 L2 : List Literal) (s1 s2 : List Bool),
      L1.flatMap encodeLiteral ++ ([true, true] ++ s1) =
        L2.flatMap encodeLiteral ++ ([true, true] ++ s2) →
      L1 = L2 ∧ s1 = s2 :=
  flatMap_term_inj encodeLiteral [true, true]
    encodeLiteral_head ⟨[true], rfl⟩ encodeLiteral_inj_with_suffix

private theorem encodeClause_inj_with_suffix (c1 c2 : Clause) (s1 s2 : List Bool)
    (h : encodeClause c1 ++ s1 = encodeClause c2 ++ s2) : c1 = c2 ∧ s1 = s2 := by
  unfold encodeClause at h
  rw [List.append_assoc, List.append_assoc] at h
  exact clause_flatMap_inj c1 c2 s1 s2 h

private theorem encodeClause_ne_nil (c : Clause) : encodeClause c ≠ [] := by
  simp [encodeClause]

private theorem encodeCNF_inj_aux : ∀ (F1 F2 : CNF), encodeCNF F1 = encodeCNF F2 → F1 = F2 := by
  intro F1
  induction F1 with
  | nil =>
    intro F2 h
    cases F2 with
    | nil => rfl
    | cons c2 F2' =>
      exfalso
      simp only [encodeCNF, List.flatMap_nil, List.flatMap_cons] at h
      exact List.append_ne_nil_of_left_ne_nil (encodeClause_ne_nil c2) _ h.symm
  | cons c1 F1' ih =>
    intro F2 h
    cases F2 with
    | nil =>
      exfalso
      simp only [encodeCNF, List.flatMap_nil, List.flatMap_cons] at h
      exact List.append_ne_nil_of_left_ne_nil (encodeClause_ne_nil c1) _ h
    | cons c2 F2' =>
      simp only [encodeCNF, List.flatMap_cons] at h
      obtain ⟨hc, hrest⟩ :=
        encodeClause_inj_with_suffix c1 c2 (F1'.flatMap encodeClause) (F2'.flatMap encodeClause) h
      have hF : F1' = F2' := ih F2' hrest
      rw [hc, hF]

theorem solution : Function.Injective encodeCNF := fun F1 F2 => encodeCNF_inj_aux F1 F2
