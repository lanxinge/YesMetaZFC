import YesMetaZFC.SetTheory.LargeCardinal.TypeGameData

/-! # 从固定表项自动回收原语义接口

表项的唯一坐标把字面读取与原编译证书连起来；调用者不用提供查询正确性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_catalog_d.read_l {ω δ X P Γ κ n B U D : M.Domain} {q : Ee_queries_d M}
    (table : Ee_catalog_d hZFC ω δ X P Γ) (hk : M.mem κ δ) (hn : M.mem n ω) (hκ : M.IsLimitOrdinal κ)
    (data : Tg_ee_data_d Γ κ n B U D q) : Ee_language_d hZF ω κ n B U D q := by
  rcases q with ⟨g, h, i, e⟩
  obtain ⟨x, c, p, key, entry, row, codes⟩ := data
  obtain ⟨B', U', D', g', h', i', e', p', row', codes', language⟩ := table.2.2 κ n x c hk hn hκ key entry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row'.unique_l row
  obtain ⟨rfl, rfl, rfl, rfl⟩ := codes'.unique_l codes
  exact language

theorem Ee_catalog_d.get_l {ω δ X P Γ κ n : M.Domain} (table : Ee_catalog_d hZFC ω δ X P Γ)
    (hk : M.mem κ δ) (hn : M.mem n ω) (hκ : M.IsLimitOrdinal κ) :
    ∃ B U D, ∃ q : Ee_queries_d M, Tg_ee_data_d Γ κ n B U D q ∧ Ee_language_d hZF ω κ n B U D q := by
  obtain ⟨x, key⟩ := (I).total κ n
  obtain ⟨c, _, entry⟩ := table.2.1.2.1 x ((table.1 x).mpr ⟨κ, hk, n, hn, key⟩)
  obtain ⟨B, U, D, g, h, i, e, p, row, codes, language⟩ := table.2.2 κ n x c hk hn hκ key entry
  exact ⟨B, U, D, ⟨g, h, i, e⟩, ⟨x, c, p, key, entry, row, codes⟩, language⟩

theorem Tg_query_catalog_d.read_l {ω e δ X Γ κ k s t B U D r m b h q : M.Domain}
    (table : Tg_query_catalog_d hZFC ω e δ X Γ) (hk : M.mem κ δ)
    (request : Tg_query_request_d hZF ω κ k s t) (data : Tg_query_data_d Γ κ k s t B U D r m b h q) :
    ∃ l n, M.SuccessorOf l k ∧ M.SuccessorOf n l ∧ Tg_reply_language_d hZF ω e l n κ B U D ⟨r, b, h⟩ ∧
      Tg_max_query_d I ω l n U D m ∧ Tg_node_query_d I ω e n l U D s t k q ∧
      Formula.satisfies (⟨fun i => [ω, e, l, n, k, s, t, r, m, b, h, q].get i, fun _ => ω⟩ : Env M 12) tg_query_row0_m := by
  obtain ⟨x, c, p, a, key, entry, row, codes, tail⟩ := data
  obtain ⟨l, n, B', U', D', r', m', b', h', q', p', a', next, last, row', codes', tail', lang, max, node, base⟩ :=
    table.2 κ k s t x c key hk request entry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row'.unique_l row
  obtain ⟨rfl, rfl, rfl, rfl⟩ := codes'.unique_l codes
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M tail' tail
  exact ⟨l, n, next, last, lang, max, node, (tg_query_row_sat_l I (ZF.modelsKP hZF) _).mpr ⟨base, next, last⟩⟩

theorem Tg_program_catalog_d.read_l {ω H Γ n b z : M.Domain} {σ : Fin 7 → M.Domain}
    (table : Tg_program_catalog_d hZFC ω H Γ) (data : Tg_program_data_d Γ n b z σ) :
    ∃ a, Ts_program_d hZF ω n b σ a z := by
  obtain ⟨c, p, q, entry, row, first, last⟩ := data
  obtain ⟨b', z', p', q', s₀, s₁, s₂, s₃, s₄, s₅, s₆, a, row', first', last', prog⟩ := table.2 n c entry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row'.unique_l row
  obtain ⟨rfl, rfl, rfl, rfl⟩ := first'.unique_l first
  obtain ⟨rfl, rfl, rfl⟩ := last'.unique_l last
  have eq : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) j
  exact ⟨a, eq ▸ prog⟩

theorem Tg_program_catalog_d.get_l {ω H Γ n : M.Domain} (table : Tg_program_catalog_d hZFC ω H Γ)
    (hn : M.mem n ω) : ∃ b z, ∃ σ : Fin 7 → M.Domain, ∃ a,
      Tg_program_data_d Γ n b z σ ∧ Ts_program_d hZF ω n b σ a z := by
  obtain ⟨c, _, entry⟩ := table.1.2.1 n hn
  obtain ⟨b, z, p, q, s₀, s₁, s₂, s₃, s₄, s₅, s₆, a, row, first, last, prog⟩ := table.2 n c entry
  exact ⟨b, z, _, a, ⟨c, p, q, entry, row, first, last⟩, prog⟩

end YesMetaZFC.SetTheory.LargeCardinal
