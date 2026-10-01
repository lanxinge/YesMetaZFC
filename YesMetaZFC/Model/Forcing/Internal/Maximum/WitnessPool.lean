import YesMetaZFC.Model.Forcing.Internal.Names.Construction

/-! # 原 ZF 中的有界局部见证池

原收集模式把每个条件上出现的原公式见证收紧到一个实际名称。条目保留原
见证条件作为权重，供一般最大值与唯一见证的混合构造共用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem witness_pool_l (hZF : M.Models ZF) {n} (φ : UnarySchema n) (ρ : Env M n) :
    ∃ A, Name_d M B A ∧
      (∀ s p, Entry_d M s p A → Forces_d M B R z φ.body (ρ.push s) p) ∧
      ∀ p, M.mem p B → ∀ v, Name_d M B v → Forces_d M B R z φ.body (ρ.push v) p →
        ∃ s, Entry_d M s p A := by
  classical
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let δ := ((ρ.push B).push R).push z
  let es : Fin n → Term (n+5) := fun i => .bound ⟨i.val+5, by omega⟩
  have hδ a b : (⟨fun i => (es i).eval ((δ.push a).push b), ((δ.push a).push b).free⟩ : Env M n) = ρ := by
    cases ρ; rfl
  let ψ : BinarySchema (n+3) := {
    body := witness_m φ es (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    freeClosed := witness_closed_l _ _ _ _ _ _ _ (fun _ => rfl) rfl rfl rfl rfl rfl }
  have hψ p t : ψ.denote δ p t ↔ Name_d M B t ∧
      ∀ v, Name_d M B v → Forces_d M B R z φ.body (ρ.push v) p → Forces_d M B R z φ.body (ρ.push t) p := by
    simp only [BinarySchema.denote, ψ, witness_sat_l hZF.1, hδ]
    rfl
  obtain ⟨S₀, hS₀⟩ := ZF.collection_exists_d hZF ψ δ B (fun p _ => by
    by_cases h : ∃ v, Name_d M B v ∧ Forces_d M B R z φ.body (ρ.push v) p
    · obtain ⟨v, hv, hφ⟩ := h
      exact ⟨v, (hψ p v).mpr ⟨hv, fun _ _ _ => hφ⟩⟩
    · exact ⟨e, (hψ p e).mpr ⟨hen, fun v hv hφ => False.elim (h ⟨v, hv, hφ⟩)⟩⟩)
  let ρB : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let ν : UnarySchema 1 := { body := name_m (.bound 1) .newest }
  obtain ⟨S, hS'⟩ := ZF.separation_exists_d hZF ν ρB S₀
  have hS s : M.mem s S ↔ M.mem s S₀ ∧ Name_d M B s :=
    (hS' s).trans (and_congr_right fun _ => name_sat_l M hZF.1 (ρB.push s) _ _)
  let χ : BinarySchema (n+3) := {
    body := force_at_m φ.body (Fin.cases (.bound 1) es) (.bound 4) (.bound 3) (.bound 2) .newest
    freeClosed := force_at_closed_l _ _ _ _ _ _ φ.freeClosed (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl }
  have hχ s p : χ.denote δ s p ↔ Forces_d M B R z φ.body (ρ.push s) p := by
    simp only [BinarySchema.denote, χ, force_at_sat_l, args_cons_l, hδ]
    rfl
  obtain ⟨A, hA, _, hAE⟩ := name_comp_l M hZF χ δ B S (fun s hs => ((hS s).mp hs).2)
  refine ⟨A, hA, fun s p hsp => (hχ s p).mp (((hAE s p).mp hsp).2.2), ?_⟩
  intro p hp v hv hφ
  obtain ⟨s, hs, hw⟩ := hS₀ p hp
  obtain ⟨hsN, hw⟩ := (hψ p s).mp hw
  exact ⟨s, (hAE s p).mpr ⟨(hS s).mpr ⟨hs, hsN⟩, hp, (hχ s p).mpr (hw v hv hφ)⟩⟩

end YesMetaZFC.Model.Forcing.Internal
