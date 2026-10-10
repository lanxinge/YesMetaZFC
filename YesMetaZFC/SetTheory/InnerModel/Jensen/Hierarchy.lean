import YesMetaZFC.SetTheory.InnerModel.Jensen.Operator

/-! # Jensen 的内部 J 层级

采用宏观索引 J₀=∅、Jₐ₊₁=Rud(Jₐ∪{Jₐ})、Jλ=⋃ₐ∈λ Jₐ。
序数及递归历史均由背景模型解释，不使用 Lean 的外部序数递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def jh_env_l (a : M.Domain) : Env M 0 := ⟨Fin.elim0, fun _ => a⟩
def Jh_value_d (a Y : M.Domain) : Prop := (rc_value_s jh_op_s).schema.denote (jh_env_l a) a Y
def J_d (a Y : M.Domain) : Prop := M.IsOrdinal a ∧ Jh_value_d a Y
def jh_value_m {n} (a Y : Term n) : Formula 1 n :=
  binary_pred_m (rc_value_s jh_op_s).schema Fin.elim0 a Y
derive_free_closed jh_value_m

theorem jh_value_sat_l {n} (ρ : Env M n) (a Y : Term n) :
    Formula.satisfies ρ (jh_value_m a Y) ↔ Jh_value_d (a.eval ρ) (Y.eval ρ) := by
  rw [jh_value_m, binary_pred_sat_l]
  exact Formula.closed_env_l _ (rc_value_s jh_op_s).schema.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))

theorem jh_value_exists_l (hM : M.Models KPi) (a : M.Domain) : ∃ Y, Jh_value_d a Y := by
  obtain ⟨Y, hy⟩ := rc_value_exists_l hM jh_op_s (jh_env_l a) (jh_op_total_l hM _) (jh_op_unique_l hM _) a
  exact ⟨Y, (rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mpr hy⟩

theorem jh_value_unique_l (hM : M.Models KPi) {a X Y : M.Domain}
    (hx : Jh_value_d a X) (hy : Jh_value_d a Y) : X = Y :=
  rc_value_unique_l hM jh_op_s (jh_env_l a) (jh_op_unique_l hM _)
    ((rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp hx)
    ((rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp hy)

theorem jh_value_equation_l (hM : M.Models KPi) {a Y : M.Domain} (hy : Jh_value_d a Y) (t : M.Domain) :
    M.mem t Y ↔ ∃ b, M.mem b a ∧ ∃ X, Jh_value_d b X ∧ ∃ Z, Jh_step_d X Z ∧ M.mem t Z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have hv b X : Rc_value_d jh_op_s (jh_env_l a) b X ↔ Jh_value_d b X :=
    (rc_value_sat_l hKP.1 ..).symm.trans
      (Formula.closed_env_l _ (rc_value_s jh_op_s).schema.freeClosed rfl)
  obtain ⟨F, _, hf, he⟩ := rc_value_equation_l hM jh_op_s (jh_env_l a) (jh_op_unique_l hM _)
    ((rc_value_sat_l hKP.1 ..).mp hy)
  obtain ⟨R, P, hr, hp, hY⟩ := (jh_op_sat_l hM _ F Y).mp hf
  rw [hY t]
  change (∃ Z, M.mem Z P ∧ M.mem t Z) ↔ _
  constructor
  · rintro ⟨Z, hz, ht⟩
    obtain ⟨X, hx, hs⟩ := (hp Z).mp hz
    obtain ⟨b, hb⟩ := (hr X).mp hx
    exact ⟨b, ((he b X).mp hb).1, X, (hv b X).mp ((he b X).mp hb).2, Z, hs, ht⟩
  · rintro ⟨b, hb, X, hx, Z, hs, ht⟩
    exact ⟨Z, (hp Z).mpr ⟨X, (hr X).mpr ⟨b, (he b X).mpr ⟨hb, (hv b X).mpr hx⟩⟩, hs⟩, ht⟩

theorem jh_step_spec_l (hM : M.Models KPi) {X Y : M.Domain} (hy : Jh_step_d X Y) :
    Rd_closed_d Y ∧ M.MemberSubset X Y ∧ M.mem X Y := by
  obtain ⟨S, hs, hy⟩ := hy
  have hy := rd_closure_spec_l hM hy
  exact ⟨hy.1, fun t ht => hy.2.1 t ((hs t).mpr (Or.inl ht)), hy.2.1 X hs.predecessor_mem⟩

theorem jh_value_mono_l (hM : M.Models KPi) {a b X Y : M.Domain}
    (hab : M.MemberSubset a b) (hx : Jh_value_d a X) (hy : Jh_value_d b Y) : M.MemberSubset X Y := by
  intro t ht
  obtain ⟨c, hc, V, hv, Z, hz, ht⟩ := (jh_value_equation_l hM hx t).mp ht
  exact (jh_value_equation_l hM hy t).mpr ⟨c, hab c hc, V, hv, Z, hz, ht⟩

theorem jh_value_mem_l (hM : M.Models KPi) {a b X Y : M.Domain}
    (hab : M.mem a b) (hx : Jh_value_d a X) (hy : Jh_value_d b Y) : M.mem X Y := by
  obtain ⟨Z, hz⟩ := jh_step_exists_l hM X
  exact (jh_value_equation_l hM hy X).mpr ⟨a, hab, X, hx, Z, hz, (jh_step_spec_l hM hz).2.2⟩

theorem jh_step_transitive_l (hM : M.Models KPi) {X Y : M.Domain}
    (hx : M.TransitiveSet X) (hy : Jh_step_d X Y) : M.TransitiveSet Y := by
  obtain ⟨S, hs, hy⟩ := hy
  apply rd_closure_transitive_l hM ?_ hy
  intro a ha b hb
  apply (hs b).mpr; apply Or.inl
  exact ((hs a).mp ha).elim (fun ha => hx a ha b hb)
    (fun he => (KPi.models_iff_l.mp hM).1.1.eq_of_same_members a X he ▸ hb)

theorem jh_value_transitive_l (hM : M.Models KPi) {a Y : M.Domain}
    (hy : Jh_value_d a Y) : M.TransitiveSet Y := by
  let φ : UnarySchema 0 := { body := .forallE (.imp (jh_value_m (.bound 1) .newest)
    (Formula.isTransitive .newest)) }
  have hφ b : φ.denote (jh_env_l a) b ↔ ∀ V, Jh_value_d b V → M.TransitiveSet V := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      jh_value_sat_l, Formula.satisfies_isTransitive_iff]; rfl
  apply (hφ a).mp ((KPi.models_iff_l.mp hM).2 φ (jh_env_l a) ?_ a) Y hy
  intro b ih
  apply (hφ b).mpr
  intro V hv t ht z hz
  obtain ⟨c, hc, X, hx, Z, hs, ht⟩ := (jh_value_equation_l hM hv t).mp ht
  exact (jh_value_equation_l hM hv z).mpr
    ⟨c, hc, X, hx, Z, hs, jh_step_transitive_l hM ((hφ c).mp (ih c hc) X hx) hs t ht z hz⟩

theorem jh_zero_l (hM : M.Models KPi) {a Y : M.Domain}
    (ha : ∀ b, ¬ M.mem b a) (hy : Jh_value_d a Y) : ∀ t, ¬ M.mem t Y := by
  intro t ht
  obtain ⟨b, hb, _⟩ := (jh_value_equation_l hM hy t).mp ht
  exact ha b hb

theorem jh_step_le_l (hM : M.Models KPi) {X A Z C : M.Domain} (hXA : M.MemberSubset X A)
    (hX : M.mem X A) (hz : Jh_step_d X Z) (hc : Jh_step_d A C) : M.MemberSubset Z C := by
  obtain ⟨S, hs, hz⟩ := hz
  have hc := jh_step_spec_l hM hc
  apply (rd_closure_spec_l hM hz).2.2 C hc.1
  intro t ht
  exact hc.2.1 t (((hs t).mp ht).elim (hXA t)
    (fun he => ((KPi.models_iff_l.mp hM).1.1.eq_of_same_members t X he).symm ▸ hX))

theorem jh_successor_l (hM : M.Models KPi) {a s A B : M.Domain} (ha : M.IsOrdinal a)
    (hs : M.SuccessorOf s a) (hA : Jh_value_d a A) (hB : Jh_value_d s B) : Jh_step_d A B := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨C, hc⟩ := jh_step_exists_l hM A
  have he : B = C := by
    apply hKP.1.eq_of_same_members; intro t
    constructor
    · intro ht
      obtain ⟨b, hb, X, hx, Z, hz, ht⟩ := (jh_value_equation_l hM hB t).mp ht
      rcases (hs b).mp hb with hb | he
      · exact jh_step_le_l hM (jh_value_mono_l hM (ha.transitive b hb) hx hA)
          (jh_value_mem_l hM hb hx hA) hz hc t ht
      · have he := hKP.1.eq_of_same_members b a he; subst b
        have he := jh_value_unique_l hM hx hA; subst X
        exact jh_step_unique_l hM hz hc ▸ ht
    · intro ht
      exact (jh_value_equation_l hM hB t).mpr ⟨a, hs.predecessor_mem, A, hA, C, hc, ht⟩
  exact he.symm ▸ hc

theorem jh_limit_l (hM : M.Models KPi) {a Y : M.Domain} (ha : M.IsLimitOrdinal a)
    (hy : Jh_value_d a Y) (t : M.Domain) :
    M.mem t Y ↔ ∃ b, M.mem b a ∧ ∃ X, Jh_value_d b X ∧ M.mem t X := by
  constructor
  · intro ht
    obtain ⟨b, hb, X, hx, Z, hz, ht⟩ := (jh_value_equation_l hM hy t).mp ht
    obtain ⟨c, hc, hbc⟩ := ha.2.2 b hb
    obtain ⟨V, hv⟩ := jh_value_exists_l hM c
    exact ⟨c, hc, V, hv, (jh_value_equation_l hM hv t).mpr ⟨b, hbc, X, hx, Z, hz, ht⟩⟩
  · rintro ⟨b, hb, X, hx, ht⟩
    exact jh_value_mono_l hM (ha.1.transitive b hb) hx hy t ht

end YesMetaZFC.SetTheory.InnerModel
