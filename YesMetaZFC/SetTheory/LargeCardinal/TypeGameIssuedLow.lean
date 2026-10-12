import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssuedQuery
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor

/-! # 实际下一走法的全部节点参数留在共同低层

原实数前缀和自然数标签都是已有的有界关系图。相对极限秩层的关系闭包
把这两张图放回原字母表所在层；三个长度仍取模型自己的自然数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.issued_queries_l {ω X R μ K η C γ Z : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m) (hw : (ρ.bound 0).val = ω)
    (hZ : M.mem Z X) (rank : Vr_d X γ Z) (limit : M.IsLimitOrdinal γ)
    (omega : M.mem ω Z) (letters : M.mem (ρ.bound 6).val Z) :
    ∃ ψ χ : Env (rt_model_l C nc) 12,
      Formula.satisfies ψ tg_query_row0_m ∧
      (∀ i : Fin 5, (ψ.bound (i.castAdd 7)).val =
        [(ρ.bound 0).val, (ρ.bound 1).val, (ρ.bound 27).val, (ρ.bound 28).val, (ρ.bound 26).val].get i) ∧
      M.mem (ψ.bound 11).val (ρ.bound 25).val ∧ (∀ i : Fin 7, M.mem (ψ.bound (i.castAdd 5)).val Z) ∧
      Formula.satisfies χ tg_candidate0_m ∧
      (∀ i : Fin 5, (χ.bound (i.castAdd 7)).val =
        [(ρ.bound 25).val, (ρ.bound 28).val, (ρ.bound 0).val, (ρ.bound 24).val, (ρ.bound 27).val].get i) := by
  have fs := (context.read_l hZF source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ρ).mp valid
  obtain ⟨_, x, s, _, _, _, r, m, b, q, f, _, digits, rest, _, _, node, query, _, _, hk, hl, hN,
    χ, same, candidate⟩ := tg_issued_query_l J ext ρ valid
  have fn {a b f : (rt_model_l C nc).Domain} (h : Fn0_d a b f) : Fn0_d a.val b.val f.val := by
    let ε : Env (rt_model_l C nc) 3 := ⟨fun i => [a, b, f].get i, fun _ => a⟩
    exact (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ε).mp
        ((fn0_sat_l ext ε (.bound 0) (.bound 1) (.bound 2)).mpr h))
  have fx := fn digits.1
  have ft := fn state.labels
  have rest := (rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair s x (ρ.bound 26)).mp rest
  have trans := rank.transitive_l hZF source.transitive hZ
  have natural (v : (rt_model_l C nc).Domain) (hv : (rt_model_l C nc).mem v (ρ.bound 0)) : M.mem v.val Z :=
    trans ω omega v.val (hw ▸ hv)
  have hs := rank.relation_mem_l hZF source.transitive hZ limit omega letters
    (source.transitive C context.member s.val s.property) (by
      intro p hp
      obtain ⟨i, v, pair⟩ := rest.1 p hp
      have entry := ((rest.2 i v).mp ⟨p, pair, hp⟩).2
      have bound := fx.bound_l entry
      exact ⟨i, source.omega.transitive hZF _ (hw ▸ state.round) i bound.1, v, bound.2, pair⟩)
  have ht := rank.relation_mem_l hZF source.transitive hZ limit omega omega
    (source.transitive C context.member (ρ.bound 23).val (ρ.bound 23).property) (by
      intro p hp
      obtain ⟨i, hi, v, hv, pair⟩ := ft.1 p hp
      exact ⟨i, source.omega.transitive hZF _ (hw ▸ hk) i hi, v, hw ▸ hv, pair⟩)
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff] at rules
  have he : ∀ x, ¬ M.mem x (ρ.bound 1).val := fun x hx =>
    rules.2.1 ⟨x, fs.transitive _ (ρ.bound 1).property x hx⟩ hx
  have heω := num_mem_l hZF.1 source.omega (show Num_d 0 (ρ.bound 1).val from he)
  let ψ : Env (rt_model_l C nc) 12 := ⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 27, ρ.bound 28,
    ρ.bound 26, s, ρ.bound 23, r, m, b, q, f].get i, ρ.free⟩
  refine ⟨ψ, χ, query, ?_, node, ?_, candidate, ?_⟩
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · intro i
    exact Fin.cases (hw.symm ▸ omega) (Fin.cases (trans ω omega _ heω) (Fin.cases (natural _ hl)
      (Fin.cases (natural _ hN) (Fin.cases (natural _ hk) (Fin.cases hs (Fin.cases ht (fun j => Fin.elim0 j))))))) i
  · intro i
    exact Fin.cases (congrArg Subtype.val (same 0)) (Fin.cases (congrArg Subtype.val (same 1))
      (Fin.cases (congrArg Subtype.val (same 2)) (Fin.cases (congrArg Subtype.val (same 3))
        (Fin.cases (congrArg Subtype.val (same 4)) (fun j => Fin.elim0 j))))) i

end YesMetaZFC.SetTheory.LargeCardinal
