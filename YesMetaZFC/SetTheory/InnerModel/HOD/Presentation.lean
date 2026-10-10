import YesMetaZFC.SetTheory.InnerModel.HOD.Coding
import YesMetaZFC.SetTheory.InnerModel.OD.Relations
import YesMetaZFC.SetTheory.TransitiveClosure
import YesMetaZFC.SetTheory.Collapse.RelationExistence

/-! # HOD[A] 对象的序数关系呈现

先编码 TC({x}) 的全部对象，再把真实隶属关系回拉到有界定义码上。所得载体和
关系都在 OD[A] 中；解码器正是这份内部良基关系的总坍塌图。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 序数代码、可定义关系与包含原对象的实际坍塌一次构造。 -/
theorem hb_presentation_l {A x : M.Domain} (hx : Hb_d A x) :
    ∃ κ C R T F, M.IsOrdinal κ ∧ M.MemberSubset C κ ∧
      (∀ p, M.mem p R → ∃ a b, M.mem a C ∧ M.mem b C ∧ KPair_d M p a b) ∧
      Ob_d A C ∧ Ob_d A R ∧ Fn0_d C T F ∧ Wc_graph_d C R F ∧ ∃ a, Rd_entry_d a x F := by
  obtain ⟨S, htS, hxS, hS⟩ := hx
  obtain ⟨T, ht⟩ := ZF.tc_exists_l I hZF x
  have hT y (hy : M.mem y T) : Ob_d A y := oa_bracket_l.mp (hS y (ht.2.2 S htS hxS y hy))
  have hoT : Ob_d A T := by
    let φ : UnarySchema 1 := { body := tc_m (.bound 1) .newest }
    exact ob_closed_l hZF A φ ⟨fun _ => x, fun _ => x⟩ (fun _ => hT x ht.2.1)
      (fun V => (tc_sat_l _ _ _).trans
        ⟨fun hV => tc_unique_l hZF.1 hV ht, fun he => he.symm ▸ ht⟩)
  obtain ⟨κ, C, F, hκ, hCκ, hoC, fn, entry, cover⟩ := ob_code_graph_l hZF hoT hT
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let φ : BinarySchema 1 := {
    body := .existsE (.existsE (.conj (ob_eval_m (.bound 3) (.bound 4) (.bound 1))
      (.conj (ob_eval_m (.bound 2) (.bound 4) .newest) (.mem (.bound 1) .newest)))) }
  have sat a b : φ.denote ρ a b ↔ ∃ y z, Ob_eval_d I a A y ∧ Ob_eval_d I b A z ∧ M.mem y z := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      ob_eval_sat_l I hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨R, hoR, hR, rel⟩ := ob_relation_l hZF A φ ρ (fun _ => ob_parameter_l hZF A) hoC
  have bound p (hp : M.mem p R) : ∃ a b, M.mem a C ∧ M.mem b C ∧ KPair_d M p a b := by
    obtain ⟨a, b, hab⟩ := hR.1 p hp
    exact ⟨a, b, (hR.2 a b ⟨p, hab, hp⟩).1, (hR.2 a b ⟨p, hab, hp⟩).2, hab⟩
  refine ⟨κ, C, R, T, F, hκ, hCκ, bound, hoC, hoR, fn, ⟨?_, ?_⟩, cover x ht.2.1⟩
  · intro p hp
    obtain ⟨a, _, y, _, hab⟩ := fn.1 p hp
    exact ⟨a, y, hab⟩
  · intro a y hay
    obtain ⟨ha, hy⟩ := (entry a y).mp hay
    refine ⟨ha, fun b hb _ => (fn.2.1 b hb).imp fun _ h => h.2, fun z => ?_⟩
    constructor
    · intro hz
      obtain ⟨b, hbz⟩ := cover z (ht.1 y (fn.bound_l hay).2 z hz)
      obtain ⟨hb, hzb⟩ := (entry b z).mp hbz
      exact ⟨b, hb, (rel b a).mpr ⟨hb, ha, (sat b a).mpr ⟨z, y, hzb, hy, hz⟩⟩, hbz⟩
    · rintro ⟨b, _, hba, hbz⟩
      obtain ⟨v, w, hv, hw, hvw⟩ := (sat b a).mp ((rel b a).mp hba).2.2
      have eqv := ob_eval_unique_l I hZF hv ((entry b z).mp hbz).2
      have eqw := ob_eval_unique_l I hZF hw hy
      exact eqv ▸ eqw ▸ hvw

end YesMetaZFC.SetTheory.InnerModel
