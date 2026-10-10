import YesMetaZFC.SetTheory.InnerModel.Computation.Totality

/-! # 以集合程序计算真值

假值为 ∅，真值为 {∅}。逻辑操作编译为配对、差集和集合有界循环。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cp_pair_l {n} (p q : Cp_code n) : Cp_code n := .op .pair p q .zero
def cp_diff_l {n} (p q : Cp_code n) : Cp_code n := .op .diff p q .zero
def cp_one_l {n} : Cp_code n := cp_pair_l .zero .zero
def cp_not_l {n} (p : Cp_code n) : Cp_code n := cp_diff_l cp_one_l p
def cp_and_l {n} (p q : Cp_code n) : Cp_code n := cp_diff_l p (cp_diff_l p q)
def cp_or_l {n} (p q : Cp_code n) : Cp_code n := cp_not_l (cp_and_l (cp_not_l p) (cp_not_l q))
def cp_imp_l {n} (p q : Cp_code n) : Cp_code n := cp_not_l (cp_diff_l p q)
def cp_iff_l {n} (p q : Cp_code n) : Cp_code n := cp_and_l (cp_imp_l p q) (cp_imp_l q p)
def cp_subset_l {n} (p q : Cp_code n) : Cp_code n := cp_not_l (.bunion (cp_diff_l p q) cp_one_l)
def cp_member_l {n} (p q : Cp_code n) : Cp_code n := cp_subset_l (cp_pair_l p p) q
def cp_equal_l {n} (p q : Cp_code n) : Cp_code n := cp_and_l (cp_subset_l p q) (cp_subset_l q p)

def Cp_bit_d (P : Prop) (y : M.Domain) : Prop := ∀ t, M.mem t y ↔ (∀ z, ¬ M.mem z t) ∧ P
def Cp_decides_d {n} (p : Cp_code n) (ρ : Env M n) (P : Prop) : Prop :=
  ∀ y, Cp_eval_d p ρ y → Cp_bit_d P y

theorem Cp_decides_d.congr_l {n} {p : Cp_code n} {ρ : Env M n} {P Q : Prop}
    (h : Cp_decides_d p ρ P) (he : P ↔ Q) : Cp_decides_d p ρ Q :=
  fun y hy t => (h y hy t).trans (and_congr_right fun _ => he)

theorem cp_decide_iff_l (hKP : M.Models KP) {n} {p : Cp_code n} {ρ : Env M n} {P : Prop}
    (h : Cp_decides_d p ρ P) (y : M.Domain) : Cp_eval_d p ρ y ↔ Cp_bit_d P y := by
  refine ⟨h y, fun hy => ?_⟩
  obtain ⟨z, hz⟩ := cp_eval_total_l hKP p ρ
  have he := hKP.1.eq_of_same_members z y (fun t => (h z hz t).trans (hy t).symm)
  exact he ▸ hz

theorem cp_op_iff_l (hE : Extensional M) {n} {p q r : Cp_code n} {ρ : Env M n} {a b c : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) (hr : Cp_eval_d r ρ c) (k : Rd_sym) (y : M.Domain) :
    Cp_eval_d (.op k p q r) ρ y ↔ Rd_fun_d k a b c y := by
  constructor
  · rintro ⟨a', b', c', ha, hb, hc, hy⟩
    have he := cp_eval_unique_l hE p ρ ha hp; subst a'
    have he := cp_eval_unique_l hE q ρ hb hq; subst b'
    have he := cp_eval_unique_l hE r ρ hc hr; subst c'
    exact hy
  · exact fun hy => ⟨a, b, c, hp, hq, hr, hy⟩

theorem cp_pair_iff_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {a b : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) (y : M.Domain) :
    Cp_eval_d (cp_pair_l p q) ρ y ↔ Pair_d M y a b := by
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  exact cp_op_iff_l hKP.1 hp hq (show Cp_eval_d .zero ρ e from he) .pair y

theorem cp_diff_iff_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {a b : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) (y : M.Domain) :
    Cp_eval_d (cp_diff_l p q) ρ y ↔ ∀ t, M.mem t y ↔ M.mem t a ∧ ¬ M.mem t b := by
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  exact cp_op_iff_l hKP.1 hp hq (show Cp_eval_d .zero ρ e from he) .diff y

theorem cp_zero_bit_l {n} (ρ : Env M n) : Cp_decides_d .zero ρ False :=
  fun _ hy t => ⟨fun ht => (hy t ht).elim, fun h => h.2.elim⟩

theorem cp_one_bit_l (hKP : M.Models KP) {n} (ρ : Env M n) : Cp_decides_d cp_one_l ρ True := by
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  intro y hy t
  have hz : Cp_eval_d .zero ρ e := he
  have hp := (cp_pair_iff_l hKP hz hz y).mp hy
  exact (hp t).trans ⟨fun h => h.elim (fun h => h.symm ▸ ⟨he, trivial⟩) (fun h => h.symm ▸ ⟨he, trivial⟩),
    fun ⟨ht, _⟩ => Or.inl (hKP.1.eq_of_same_members t e (fun z => iff_of_false (ht z) (he z)))⟩

theorem cp_diff_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {P Q : Prop}
    (hp : Cp_decides_d p ρ P) (hq : Cp_decides_d q ρ Q) : Cp_decides_d (cp_diff_l p q) ρ (P ∧ ¬ Q) := by
  obtain ⟨a, ha⟩ := cp_eval_total_l hKP p ρ
  obtain ⟨b, hb⟩ := cp_eval_total_l hKP q ρ
  intro y hy t
  have hy := (cp_diff_iff_l hKP ha hb y).mp hy
  rw [hy t, hp a ha t, hq b hb t]
  exact ⟨fun ⟨⟨he, hp⟩, hn⟩ => ⟨he, hp, fun hq => hn ⟨he, hq⟩⟩,
    fun ⟨he, hp, hn⟩ => ⟨⟨he, hp⟩, fun hq => hn hq.2⟩⟩

theorem cp_not_bit_l (hKP : M.Models KP) {n} {p : Cp_code n} {ρ : Env M n} {P : Prop}
    (hp : Cp_decides_d p ρ P) : Cp_decides_d (cp_not_l p) ρ (¬ P) :=
  (cp_diff_bit_l hKP (cp_one_bit_l hKP ρ) hp).congr_l ⟨And.right, fun h => ⟨trivial, h⟩⟩

theorem cp_and_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {P Q : Prop}
    (hp : Cp_decides_d p ρ P) (hq : Cp_decides_d q ρ Q) : Cp_decides_d (cp_and_l p q) ρ (P ∧ Q) :=
  (cp_diff_bit_l hKP hp (cp_diff_bit_l hKP hp hq)).congr_l
    ⟨fun ⟨hp, hn⟩ => ⟨hp, Classical.byContradiction (fun hq => hn ⟨hp, hq⟩)⟩,
      fun ⟨hp, hq⟩ => ⟨hp, fun hn => hn.2 hq⟩⟩

theorem cp_or_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {P Q : Prop}
    (hp : Cp_decides_d p ρ P) (hq : Cp_decides_d q ρ Q) : Cp_decides_d (cp_or_l p q) ρ (P ∨ Q) := by
  apply (cp_not_bit_l hKP (cp_and_bit_l hKP (cp_not_bit_l hKP hp) (cp_not_bit_l hKP hq))).congr_l
  exact ⟨fun h => Classical.byContradiction (fun hn => h ⟨fun hp => hn (Or.inl hp), fun hq => hn (Or.inr hq)⟩),
    fun h hn => h.elim hn.1 hn.2⟩

theorem cp_imp_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {P Q : Prop}
    (hp : Cp_decides_d p ρ P) (hq : Cp_decides_d q ρ Q) : Cp_decides_d (cp_imp_l p q) ρ (P → Q) :=
  (cp_not_bit_l hKP (cp_diff_bit_l hKP hp hq)).congr_l
    ⟨fun hn hp => Classical.byContradiction (fun hq => hn ⟨hp, hq⟩), fun h hn => hn.2 (h hn.1)⟩

theorem cp_iff_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {P Q : Prop}
    (hp : Cp_decides_d p ρ P) (hq : Cp_decides_d q ρ Q) : Cp_decides_d (cp_iff_l p q) ρ (P ↔ Q) :=
  (cp_and_bit_l hKP (cp_imp_bit_l hKP hp hq) (cp_imp_bit_l hKP hq hp)).congr_l
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem cp_bunion_bit_l (hKP : M.Models KP) {n} {p : Cp_code n} {q : Cp_code (n + 1)} {ρ : Env M n}
    {X : M.Domain} {P : M.Domain → Prop} (hp : Cp_eval_d p ρ X)
    (hq : ∀ z, M.mem z X → Cp_decides_d q (ρ.push z) (P z)) :
    Cp_decides_d (.bunion p q) ρ (∃ z, M.mem z X ∧ P z) := by
  intro y hy t
  obtain ⟨X', R, hx, ht, hr, hy⟩ := hy
  have he := cp_eval_unique_l hKP.1 p ρ hx hp; subst X'
  rw [hy t]
  constructor
  · rintro ⟨v, hvR, htv⟩
    obtain ⟨z, hz, hv⟩ := (hr v).mp hvR
    have h := (hq z hz v hv t).mp htv
    exact ⟨h.1, z, hz, h.2⟩
  · rintro ⟨he, z, hz, hp⟩
    obtain ⟨v, hv⟩ := ht z hz
    exact ⟨v, (hr v).mpr ⟨z, hz, hv⟩, (hq z hz v hv t).mpr ⟨he, hp⟩⟩

theorem cp_subset_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {a b : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) :
    Cp_decides_d (cp_subset_l p q) ρ (M.MemberSubset a b) := by
  obtain ⟨D, hd⟩ := cp_eval_total_l hKP (cp_diff_l p q) ρ
  have hD := (cp_diff_iff_l hKP hp hq D).mp hd
  apply (cp_not_bit_l hKP (cp_bunion_bit_l hKP hd (fun _ _ => cp_one_bit_l hKP _))).congr_l
  exact ⟨fun hn z hz => Classical.byContradiction (fun h => hn ⟨z, (hD z).mpr ⟨hz, h⟩, trivial⟩),
    fun h ⟨z, hz, _⟩ => ((hD z).mp hz).2 (h z ((hD z).mp hz).1)⟩

theorem cp_member_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {a b : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) : Cp_decides_d (cp_member_l p q) ρ (M.mem a b) := by
  obtain ⟨S, hs⟩ := cp_eval_total_l hKP (cp_pair_l p p) ρ
  have hS := (cp_pair_iff_l hKP hp hp S).mp hs
  exact (cp_subset_bit_l hKP hs hq).congr_l ⟨fun h => h a ((hS a).mpr (Or.inl rfl)),
    fun h t ht => ((hS t).mp ht).elim (fun he => he.symm ▸ h) (fun he => he.symm ▸ h)⟩

theorem cp_equal_bit_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {a b : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) : Cp_decides_d (cp_equal_l p q) ρ (a = b) := by
  apply (cp_and_bit_l hKP (cp_subset_bit_l hKP hp hq) (cp_subset_bit_l hKP hq hp)).congr_l
  exact ⟨fun h => hKP.1.eq_of_same_members a b (fun t => ⟨h.1 t, h.2 t⟩),
    fun he => ⟨fun _ h => he ▸ h, fun _ h => he.symm ▸ h⟩⟩

end YesMetaZFC.SetTheory.InnerModel
