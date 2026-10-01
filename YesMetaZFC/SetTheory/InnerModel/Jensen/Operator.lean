import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Hull
import YesMetaZFC.SetTheory.KP.Sigma1Operations

/-! # Jensen 层级的 Σ₁ 后继算子和递归算子

后继是 Rud(X∪{X})。递归算子取所有前值的后继之并，因此零、后继和极限
三种情形共享同一个总的 Σ₁ 正规形，不需要对内部序数作外部分类。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rd_unary_s (k : Rd_sym) : S1_binary 0 := S1_binary.of_delta0 {
  body := rd_graph_m k (.bound 1) (.bound 1) (.bound 1) .newest
  delta0 := rd_graph_delta_l .. }

theorem rd_unary_sat_l (hKP : M.Models KP) (k : Rd_sym) (ρ : Env M 0) (x y : M.Domain) :
    (rd_unary_s k).schema.denote ρ x y ↔ Rd_fun_d k x x x y := by
  rw [rd_unary_s, S1_binary.of_delta0_sat_l]
  exact rd_graph_sat_l hKP _ _ _ _ _ _

def jh_adjoin_s : S1_binary 0 := S1_binary.of_delta0 {
  body := KP.succ0_m .newest (.bound 1), delta0 := KP.succ0_delta_l .. }
def jh_step_s : S1_binary 0 := jh_adjoin_s.comp rd_closure_s
def Jh_step_d (X Y : M.Domain) : Prop := ∃ S, M.SuccessorOf S X ∧ Rd_closure_d S Y

theorem jh_step_sat_l (hKP : M.Models KP) (ρ : Env M 0) (X Y : M.Domain) :
    jh_step_s.schema.denote ρ X Y ↔ Jh_step_d X Y := by
  rw [jh_step_s, S1_binary.comp_sat_l hKP]
  apply exists_congr; intro S
  rw [rd_closure_sat_l hKP.1, jh_adjoin_s, S1_binary.of_delta0_sat_l]
  exact and_congr (KP.succ0_sat_l hKP.1 _ _ _) Iff.rfl

theorem jh_step_exists_l (hM : M.Models KPi) (X : M.Domain) : ∃ Y, Jh_step_d X Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨S, hs⟩ := KP.exists_insert hKP X X
  obtain ⟨Y, hy⟩ := rd_closure_exists_l hM S
  exact ⟨Y, S, fun t => (hs t).trans (or_congr_right
    ⟨fun he => he ▸ (fun _ => Iff.rfl), hKP.1.eq_of_same_members _ _⟩), hy⟩

theorem jh_step_unique_l (hM : M.Models KPi) {X Y Z : M.Domain}
    (hy : Jh_step_d X Y) (hz : Jh_step_d X Z) : Y = Z := by
  obtain ⟨S, hs, hy⟩ := hy
  obtain ⟨T, ht, hz⟩ := hz
  have he := Structure.SuccessorOf.eq (KPi.models_iff_l.mp hM).1.1 hs ht; subst T
  exact rd_closure_unique_l hM hy hz

def jh_op_s : S1_binary 0 := (rd_unary_s .range).comp (jh_step_s.image.comp (rd_unary_s .union))

theorem jh_op_sat_l (hM : M.Models KPi) (ρ : Env M 0) (F Y : M.Domain) :
    jh_op_s.schema.denote ρ F Y ↔ ∃ R P, Rd_fun_d .range F F F R ∧
      (∀ v, M.mem v P ↔ ∃ x, M.mem x R ∧ Jh_step_d x v) ∧ Rd_fun_d .union P P P Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have hi R P := S1_binary.image_sat_l hKP jh_step_s ρ R P
    (fun x _ => (jh_step_exists_l hM x).imp (fun y h => (jh_step_sat_l hKP ρ x y).mpr h))
    (fun _ _ _ _ hy hz => jh_step_unique_l hM ((jh_step_sat_l hKP ..).mp hy) ((jh_step_sat_l hKP ..).mp hz))
  simp only [jh_op_s, S1_binary.comp_sat_l hKP, rd_unary_sat_l hKP, hi, jh_step_sat_l hKP]
  exact ⟨fun ⟨R, hr, P, hp, hy⟩ => ⟨R, P, hr, hp, hy⟩, fun ⟨R, P, hr, hp, hy⟩ => ⟨R, hr, P, hp, hy⟩⟩

theorem jh_op_total_l (hM : M.Models KPi) (ρ : Env M 0) (F : M.Domain) :
    ∃ Y, jh_op_s.schema.denote ρ F Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨R, hr⟩ := rd_fun_exists_l hKP .range F F F
  obtain ⟨P, hp⟩ := KP.s1_image_l hKP jh_step_s ρ R
    (fun x _ => (jh_step_exists_l hM x).imp (fun y h => (jh_step_sat_l hKP ρ x y).mpr h))
    (fun _ _ _ _ hy hz => jh_step_unique_l hM ((jh_step_sat_l hKP ..).mp hy) ((jh_step_sat_l hKP ..).mp hz))
  obtain ⟨Y, hy⟩ := rd_fun_exists_l hKP .union P P P
  exact ⟨Y, (jh_op_sat_l hM ρ F Y).mpr ⟨R, P, hr, by simpa only [jh_step_sat_l hKP] using hp, hy⟩⟩

theorem jh_op_unique_l (hM : M.Models KPi) (ρ : Env M 0) (F Y Z : M.Domain)
    (hy : jh_op_s.schema.denote ρ F Y) (hz : jh_op_s.schema.denote ρ F Z) : Y = Z := by
  obtain ⟨R, P, hr, hp, hy⟩ := (jh_op_sat_l hM ρ F Y).mp hy
  obtain ⟨R', P', hr', hp', hz⟩ := (jh_op_sat_l hM ρ F Z).mp hz
  have he := rd_fun_unique_l (KPi.models_iff_l.mp hM).1.1 hr hr'; subst R'
  have he := (KPi.models_iff_l.mp hM).1.1.eq_of_same_members P P' (fun t => (hp t).trans (hp' t).symm); subst P'
  exact rd_fun_unique_l (KPi.models_iff_l.mp hM).1.1 hy hz

end YesMetaZFC.SetTheory.InnerModel
