import YesMetaZFC.SetTheory.InnerModel.Order.Operator

/-! # Jensen 有序微层级的内部构造

Js_state 同时递归载体及其序；索引是模型内部的集合。序数索引处的载体将满足
S₀=∅、Sᵅ⁺¹=s(Sᵅ∪{Sᵅ})、Sλ=⋃ᵝ<λ Sᵝ。这里先给出无条件的递归方程。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def js_env_l (a : M.Domain) : Env M 0 := ⟨Fin.elim0, fun _ => a⟩
def Js_state_d (a p : M.Domain) : Prop := (rc_value_s rw_op_s).schema.denote (js_env_l a) a p
theorem js_state_env_l (ρ : Env M 0) (a p : M.Domain) :
    (rc_value_s rw_op_s).schema.denote ρ a p ↔ Js_state_d a p :=
  Formula.closed_env_l _ (rc_value_s rw_op_s).schema.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))
def js_state_m {n} (a p : Term n) : Formula 1 n := binary_pred_m (rc_value_s rw_op_s).schema Fin.elim0 a p
derive_free_closed js_state_m
theorem js_state_sat_l {n} (ρ : Env M n) (a p : Term n) :
    Formula.satisfies ρ (js_state_m a p) ↔ Js_state_d (a.eval ρ) (p.eval ρ) := by
  rw [js_state_m, binary_pred_sat_l, js_state_env_l]

theorem js_state_exists_l (hM : M.Models KPi) (a : M.Domain) : ∃ p, Js_state_d a p := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨p, hp⟩ := rc_value_exists_l hM rw_op_s (js_env_l a) (rw_op_total_l hKP _) (rw_op_unique_l hKP _) a
  exact ⟨p, (rc_value_sat_l hKP.1 ..).mpr hp⟩

theorem js_state_unique_l (hM : M.Models KPi) {a p q : M.Domain} (hp : Js_state_d a p) (hq : Js_state_d a q) : p = q :=
  rc_value_unique_l hM rw_op_s (js_env_l a) (rw_op_unique_l (KPi.models_iff_l.mp hM).1 _)
    ((rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp hp)
    ((rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp hq)

theorem js_state_equation_l (hM : M.Models KPi) {a p : M.Domain} (hp : Js_state_d a p) :
    ∃ Y, Rw_join_d Y p ∧ ∀ q, M.mem q Y ↔ ∃ b, M.mem b a ∧ ∃ r, Js_state_d b r ∧ Rw_state_d r q := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have state b r : Rc_value_d rw_op_s (js_env_l a) b r ↔ Js_state_d b r :=
    (rc_value_sat_l hKP.1 ..).symm.trans (Formula.closed_env_l _ (rc_value_s rw_op_s).schema.freeClosed rfl)
  obtain ⟨F, _, hf, he⟩ := rc_value_equation_l hM rw_op_s (js_env_l a) (rw_op_unique_l hKP _)
    ((rc_value_sat_l hKP.1 ..).mp hp)
  obtain ⟨X, Y, hx, hy, hp⟩ := (rw_op_sat_l hKP ..).mp hf
  refine ⟨Y, hp, fun q => (hy q).trans ?_⟩
  constructor
  · rintro ⟨r, hrX, hrq⟩
    obtain ⟨b, hbr⟩ := (hx r).mp hrX
    exact ⟨b, ((he b r).mp hbr).1, r, (state b r).mp ((he b r).mp hbr).2, hrq⟩
  · rintro ⟨b, hb, r, hr, hrq⟩
    exact ⟨r, (hx r).mpr ⟨b, (he b r).mpr ⟨hb, (state b r).mpr hr⟩⟩, hrq⟩

def Js_value_d (a U R : M.Domain) : Prop := ∃ p, Js_state_d a p ∧ KPair_d M p U R

theorem js_state_pair_l (hM : M.Models KPi) {a p : M.Domain} (hp : Js_state_d a p) : ∃ U R, KPair_d M p U R := by
  obtain ⟨_, ⟨U, R, _, _, hp⟩, _⟩ := js_state_equation_l hM hp
  exact ⟨U, R, hp⟩

theorem js_value_exists_l (hM : M.Models KPi) (a : M.Domain) : ∃ U R, Js_value_d a U R := by
  obtain ⟨p, hp⟩ := js_state_exists_l hM a
  obtain ⟨U, R, hpUR⟩ := js_state_pair_l hM hp
  exact ⟨U, R, p, hp, hpUR⟩
theorem js_value_unique_l (hM : M.Models KPi) {a U R V S : M.Domain} (h : Js_value_d a U R) (g : Js_value_d a V S) :
    U = V ∧ R = S := by
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨q, hq, g⟩ := g
  have he := js_state_unique_l hM hp hq; subst q
  exact kpair_injective_l M h g

theorem js_value_equation_l (hM : M.Models KPi) {a U R : M.Domain} (h : Js_value_d a U R) :
    ∃ Y, Rp_union_d false Y U ∧ Rp_union_d true Y R ∧ ∀ A S,
      Rd_entry_d A S Y ↔ ∃ b, M.mem b a ∧ ∃ V T, Js_value_d b V T ∧ Rw_successor_d V T A S := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨p, hp, hpair⟩ := h
  obtain ⟨Y, hy, hY⟩ := js_state_equation_l hM hp
  refine ⟨Y, (hy.coordinates_l hpair).1, (hy.coordinates_l hpair).2, fun A S => ?_⟩
  constructor
  · rintro ⟨q, hq, hqY⟩
    obtain ⟨b, hb, r, hr, hrq⟩ := (hY q).mp hqY
    obtain ⟨V, T, hrVT⟩ := js_state_pair_l hM hr
    exact ⟨b, hb, V, T, ⟨r, hr, hrVT⟩, (rw_state_pair_l hKP.1 hrVT hq).mp hrq⟩
  · rintro ⟨b, hb, V, T, ⟨r, hr, hrVT⟩, h⟩
    obtain ⟨q, hq⟩ := (kp_pair_l hKP).total A S
    exact ⟨q, hq, (hY q).mpr ⟨b, hb, r, hr, (rw_state_pair_l hKP.1 hrVT hq).mpr h⟩⟩

end YesMetaZFC.SetTheory.InnerModel
