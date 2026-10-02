import YesMetaZFC.SetTheory.InnerModel.Separation.Definable
import YesMetaZFC.SetTheory.InnerModel.Separation.Enclosure

/-! # 有限基闭包内的 Δ₀ 分离

先构造实际原公式的真值表，再固定参数元组取纤维，最后与源集合相交。
分离集属于闭包是该构造的结论，不作为闭包定义或证明前提。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rd_separation_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (ht : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U)
    {n} (φ : Delta0UnarySchema n) (ρ : Env M n) (hρ : ∀ i, M.mem (ρ.bound i) U)
    {X : M.Domain} (hX : M.mem X U) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.toUnarySchema.denote ρ x := by
  let hn : Nonempty {x : M.Domain // M.mem x U} := ⟨⟨X, hX⟩⟩
  let η : Env (rt_model_l U hn) n := ⟨fun i => ⟨ρ.bound i, hρ i⟩, fun _ => ⟨X, hX⟩⟩
  have hφ (x : (rt_model_l U hn).Domain) :
      φ.toUnarySchema.denote η x ↔ φ.toUnarySchema.denote ρ x.val := by
    apply (rt_model_delta_l hu hn φ.delta0 (η.push x)).trans
    exact Formula.closed_env_l _ φ.freeClosed (funext (Fin.cases rfl (fun _ => rfl)))
  obtain ⟨S, hSC, hs⟩ := rt_definable_l hKP hC hU (fun x hx => ht U hU x hx) hu hn φ.toUnarySchema η
  have hs x : M.mem x S ↔ M.mem x U ∧ φ.toUnarySchema.denote ρ x := (hs x).trans
    ⟨fun ⟨hx, h⟩ => ⟨hx, (hφ ⟨x, hx⟩).mp h⟩, fun ⟨hx, h⟩ => ⟨hx, (hφ ⟨x, hx⟩).mpr h⟩⟩
  have hXC := ht U hU X hX
  obtain ⟨D, hDC, hD⟩ := hC.exists_l hKP .diff hXC hSC hXC
  obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .diff hXC hDC hXC
  refine ⟨Y, hYC, fun x => ?_⟩
  rw [hY x]; change (M.mem x X ∧ ¬ M.mem x D) ↔ _
  rw [hD x]; change (M.mem x X ∧ ¬ (M.mem x X ∧ ¬ M.mem x S)) ↔ _
  rw [hs x]
  exact ⟨fun ⟨hx, hn⟩ => ⟨hx, (Classical.byContradiction (fun h => hn ⟨hx, h⟩)).2⟩,
    fun ⟨hx, hp⟩ => ⟨hx, fun h => h.2 ⟨hu X hX x hx, hp⟩⟩⟩

theorem rd_bounded_filter_l (hKP : M.Models KP) {C B : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hBC : M.mem B C) (hb : M.TransitiveSet B) {n}
    (φ : Delta0UnarySchema n) (ρ : Env M n) (hρ : ∀ i, M.mem (ρ.bound i) C ∧ M.MemberSubset (ρ.bound i) B) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x B ∧ φ.toUnarySchema.denote ρ x := by
  obtain ⟨T, hTC, ht, _, hL⟩ := rd_finite_enclosed_l hKP hC hBC hb (B :: List.ofFn ρ.bound) (by
    intro A ha; rcases List.mem_cons.mp ha with he | ha
    · exact he ▸ rd_transitive_enclosed_l hKP hC hBC hb
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨T, hTC, ht, _, hAT⟩ := rd_bounded_enclosed_l hKP hC hBC hb (hρ i).1 (hρ i).2
      exact ⟨T, hTC, ht, hAT⟩)
  exact rd_separation_l hKP hC hc hTC ht φ ρ
    (fun i => hL _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))) (hL B (List.mem_cons_self ..))

end YesMetaZFC.SetTheory.InnerModel
