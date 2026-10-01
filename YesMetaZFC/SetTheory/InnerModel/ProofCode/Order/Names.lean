import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Bound

/-! # 分级规范码名 (序数界,内部高度,构造树)

第一坐标 α 要求构造树属于 rud(α)，第二坐标给出语法高度界。
同一树可以有多个名字；以下固定所有名字的次序，不预先选择最小名字。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pn_name_d (v a h c : M.Domain) : Prop := Rd_triple_d v a h c ∧ M.IsOrdinal a ∧ KP.N0_d h ∧
  Ps_height_d h c ∧ ∃ C, Rd_closure_d a C ∧ M.mem c C
def Pn_valid_d (v : M.Domain) : Prop := ∃ a h c, Pn_name_d v a h c

def Pn_key_d (a h c b m d : M.Domain) : Prop :=
  M.mem a b ∨ (a = b ∧ (M.mem h m ∨ (h = m ∧ Po_lt_d c d)))
def Pn_lt_d (v w : M.Domain) : Prop := ∃ a h c b m d,
  Rd_triple_d v a h c ∧ Rd_triple_d w b m d ∧ Pn_key_d a h c b m d

theorem pn_triple_unique_l (hE : Extensional M) {v w a h c : M.Domain}
    (hv : Rd_triple_d v a h c) (hw : Rd_triple_d w a h c) : v = w := by
  obtain ⟨p, hp, hv⟩ := hv
  obtain ⟨q, hq, hw⟩ := hw
  have he := kpair_unique_l M hE hp hq; subst q
  exact kpair_unique_l M hE hv hw

theorem pn_lt_iff_l {v w a h c b m d : M.Domain} (hv : Rd_triple_d v a h c) (hw : Rd_triple_d w b m d) :
    Pn_lt_d v w ↔ Pn_key_d a h c b m d := by
  constructor
  · rintro ⟨a', h', c', b', m', d', hv', hw', he⟩
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hv' hv
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hw' hw
    exact he
  · exact fun he => ⟨a, h, c, b, m, d, hv, hw, he⟩

theorem pn_name_exists_l (hM : M.Models KPi) {c : M.Domain} (hc : Ps_valid_d c) : ∃ v a h, Pn_name_d v a h c := by
  obtain ⟨a, C, ha, hC, hcC⟩ := po_code_bound_l hM hc
  obtain ⟨n, T, F, hf, hcn⟩ := hc
  obtain ⟨v, hv⟩ := pc_triple_exists_l (KPi.models_iff_l.mp hM).1 a n c
  exact ⟨v, a, n, hv, ha, (hf.at_l hcn).2.2.1, ⟨n, Or.inr rfl, T, F, hf, hcn⟩, C, hC, hcC⟩

def Pn_eval_d (v x : M.Domain) : Prop := ∃ a h c, Pn_name_d v a h c ∧ Pc_eval_d c x

theorem pn_eval_total_l (hM : M.Models KPi) {v : M.Domain} (hv : Pn_valid_d v) : ∃ x, Pn_eval_d v x := by
  obtain ⟨a, h, c, hv⟩ := hv
  obtain ⟨x, hx⟩ := ps_eval_total_l hM hv.2.2.2.1.valid_l
  exact ⟨x, a, h, c, hv, hx⟩

theorem pn_eval_unique_l (hM : M.Models KPi) {v x y : M.Domain} (hx : Pn_eval_d v x) (hy : Pn_eval_d v y) : x = y := by
  obtain ⟨a, h, c, hv, hx⟩ := hx
  obtain ⟨b, m, d, hw, hy⟩ := hy
  obtain ⟨_, _, rfl⟩ := pc_triple_inj_l hv.1 hw.1
  exact pc_eval_unique_l hM hx hy

theorem pn_cover_l (hM : M.Models KPi) (x : M.Domain) : L_d x ↔ ∃ v, Pn_eval_d v x := by
  constructor
  · intro hx
    obtain ⟨c, hc, hx⟩ := (pc_valid_cover_l hM x).mp hx
    obtain ⟨v, a, h, hv⟩ := pn_name_exists_l hM hc
    exact ⟨v, a, h, c, hv, hx⟩
  · rintro ⟨v, a, h, c, _, hx⟩; exact pc_eval_in_l_l hM hx

def Pn_proj_d (i : Fin 3) (T v x : M.Domain) : Prop := ∃ a, M.mem a T ∧ ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧
  Rd_triple_d v a h c ∧ x = Fin.cases a (Fin.cases h (fun _ => c)) i

def pn_proj_s (i : Fin 3) : Delta0BinarySchema 1 where
  body := Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
    .conj (rd_triple0_m (.bound 4) (.bound 2) (.bound 1) .newest)
      (Formula.extensionalEq (.bound 3) (Fin.cases (.bound 2) (Fin.cases (.bound 1) (fun _ => .newest)) i))
  freeClosed := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] <;> rfl
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..) (.atom _ _ _))))

theorem pn_proj_sat_l (hE : Extensional M) (i : Fin 3) (ρ : Env M 1) (v x : M.Domain) :
    (pn_proj_s i).toBinarySchema.denote ρ v x ↔ Pn_proj_d i (ρ.bound 0) v x := by
  simp only [BinarySchema.denote, pn_proj_s, Pn_proj_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, rd_triple0_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

theorem pn_proj_value_l (i : Fin 3) {T v x a h c : M.Domain} (hv : Rd_triple_d v a h c) (hx : Pn_proj_d i T v x) :
    x = Fin.cases a (Fin.cases h (fun _ => c)) i := by
  obtain ⟨a', _, h', _, c', _, hv', hx⟩ := hx
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hv' hv
  exact hx

theorem pn_proj_unique_l (i : Fin 3) {T v x y : M.Domain} (hx : Pn_proj_d i T v x) (hy : Pn_proj_d i T v y) : x = y := by
  obtain ⟨a, _, h, _, c, _, hv, hx⟩ := hx
  exact hx.trans (pn_proj_value_l i hv hy).symm

theorem pn_fields_l {T v a h c : M.Domain} (ht : M.TransitiveSet T) (hv : M.mem v T)
    (hn : Rd_triple_d v a h c) (i : Fin 3) : Pn_proj_d i T v (Fin.cases a (Fin.cases h (fun _ => c)) i) := by
  obtain ⟨p, hp, hq⟩ := hn
  have hb := po_pair_bound_l ht hv hq
  have hc := po_pair_bound_l ht hb.2 hp
  exact ⟨a, hb.1, h, hc.1, c, hc.2, ⟨p, hp, hq⟩, rfl⟩

end YesMetaZFC.SetTheory.InnerModel
