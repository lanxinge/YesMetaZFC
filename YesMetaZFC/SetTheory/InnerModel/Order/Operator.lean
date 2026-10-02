import YesMetaZFC.SetTheory.InnerModel.Order.Join

/-! # 有序微层级的实际递归算子

先读取前值图的值域，再对各状态作规范微后继，最后分别并合载体和序关系。
每一步都有已实现的总性与单值性，直接满足内部成员递归的输入要求。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_op_d (F p : M.Domain) : Prop := ∃ X Y, Rd_fun_d .range F F F X ∧
  (∀ q, M.mem q Y ↔ ∃ r, M.mem r X ∧ Rw_state_d r q) ∧ Rw_join_d Y p
def rw_op_s : S1_binary 0 := (rd_unary_s .range).comp (rw_state_s.image.comp rw_join_s)

theorem rw_op_sat_l (hKP : M.Models KP) (ρ : Env M 0) (F p : M.Domain) :
    rw_op_s.schema.denote ρ F p ↔ Rw_op_d F p := by
  have image X Y := rw_state_s.image_sat_l hKP ρ X Y
    (fun q _ => (rw_state_total_l hKP q).imp fun r hr => (rw_state_sat_l hKP ρ q r).mpr hr)
    (fun _ _ _ _ h g => rw_state_unique_l hKP.1 ((rw_state_sat_l hKP ..).mp h) ((rw_state_sat_l hKP ..).mp g))
  simp only [rw_op_s, S1_binary.comp_sat_l hKP, rd_unary_sat_l hKP, image, rw_state_sat_l hKP, rw_join_sat_l hKP]
  exact ⟨fun ⟨X, hx, Y, hy, hp⟩ => ⟨X, Y, hx, hy, hp⟩, fun ⟨X, Y, hx, hy, hp⟩ => ⟨X, hx, Y, hy, hp⟩⟩

theorem rw_op_total_l (hKP : M.Models KP) (ρ : Env M 0) (F : M.Domain) : ∃ p, rw_op_s.schema.denote ρ F p := by
  obtain ⟨X, hx⟩ := rd_fun_exists_l hKP .range F F F
  obtain ⟨Y, hy⟩ := KP.s1_image_l hKP rw_state_s ρ X
    (fun q _ => (rw_state_total_l hKP q).imp fun r hr => (rw_state_sat_l hKP ρ q r).mpr hr)
    (fun _ _ _ _ h g => rw_state_unique_l hKP.1 ((rw_state_sat_l hKP ..).mp h) ((rw_state_sat_l hKP ..).mp g))
  obtain ⟨p, hp⟩ := rw_join_exists_l hKP Y
  exact ⟨p, (rw_op_sat_l hKP ρ F p).mpr ⟨X, Y, hx, by simpa only [rw_state_sat_l hKP] using hy, hp⟩⟩

theorem rw_op_unique_l (hKP : M.Models KP) (ρ : Env M 0) (F p q : M.Domain)
    (h : rw_op_s.schema.denote ρ F p) (g : rw_op_s.schema.denote ρ F q) : p = q := by
  obtain ⟨X, Y, hx, hy, hp⟩ := (rw_op_sat_l hKP ..).mp h
  obtain ⟨X', Y', hx', hy', hq⟩ := (rw_op_sat_l hKP ..).mp g
  have he := rd_fun_unique_l hKP.1 hx hx'; subst X'
  have he := hKP.1.eq_of_same_members Y Y' (fun r => (hy r).trans (hy' r).symm); subst Y'
  exact rw_join_unique_l hKP.1 hp hq

end YesMetaZFC.SetTheory.InnerModel
