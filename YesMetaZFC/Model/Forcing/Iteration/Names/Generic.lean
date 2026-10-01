import YesMetaZFC.Model.Forcing.Internal.Functions.Generic

/-! # 实际泛型滤子的内部名称

把每个条件的规范名称赋以该条件自身作为权重。它在任意泛型下恰好解释为
旧条件嵌入的泛型滤子，并把“名称被泛型接受”转成普通成员力迫。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Gname_d (B b γ : M.Domain) : Prop := Name_d M B γ ∧
  ∀ t p, Entry_d M t p γ ↔ M.mem p B ∧ Check_d M b p t

def gname_m {n} (B b γ : Term n) : Formula 1 n := .conj (name_m B γ)
  (.forallE (.forallE (.iff (entry_m (.bound 1) .newest γ.weaken.weaken)
    (.conj (.mem .newest B.weaken.weaken) (check_m b.weaken.weaken .newest (.bound 1))))))
derive_free_closed gname_m

theorem gname_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B b γ : Term n) :
    Formula.satisfies ρ (gname_m B b γ) ↔ Gname_d (M := M) (B.eval ρ) (b.eval ρ) (γ.eval ρ) := by
  simp only [gname_m, Gname_d, Formula.satisfies_conj_iff, name_sat_l M hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, entry_sat_l M hE,
    Formula.satisfies_mem_iff, check_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

theorem gname_exists_l (hZF : M.Models ZF) {B b} (hb : M.mem b B) : ∃ γ, Gname_d (M := M) B b γ := by
  obtain ⟨S, hS, hn⟩ := check_image_l hZF hb B
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  let φ : BinarySchema 1 := { body := check_m (.bound 2) .newest (.bound 1) }
  have hφ t p : φ.denote ρ t p ↔ Check_d M b p t := check_sat_l M hZF.1 _ _ _ _
  obtain ⟨γ, hγ, _, he⟩ := name_comp_l M hZF φ ρ B S hn
  exact ⟨γ, hγ, fun t p => (he t p).trans ⟨fun h => ⟨h.2.1, (hφ t p).mp h.2.2⟩,
    fun h => ⟨(hS t).mpr ⟨p, h.1, h.2⟩, h.1, (hφ t p).mpr h.2⟩⟩⟩

theorem gname_unique_l (hE : Extensional M) {B b γ δ}
    (hγ : Gname_d (M := M) B b γ) (hδ : Gname_d (M := M) B b δ) : γ = δ := by
  have rel {t} (ht : Name_d M B t) : ∀ v, M.mem v t → ∃ a b, KPair_d M v a b := by
    obtain ⟨S, ht, hS⟩ := ht
    exact fun v hv => (hS t ht v hv).elim fun a h => h.elim fun b h => ⟨a, b, h.1⟩
  exact entry_ext_l M hE (rel hγ.1) (rel hδ.1) (fun t p => (hγ.2 t p).trans (hδ.2 t p).symm)

theorem gname_check_l (hZF : M.Models ZF) {B R z b γ p a t}
    (O : Cond_order_d M B R z) (hb : M.mem b B) (hγ : Gname_d (M := M) B b γ)
    (ha : M.mem a B) (ht : Check_d M b a t) (hp : M.mem p B) (hpa : Entry_d M p a R) :
    Mem_force_d M B R z p t γ := mem_force_entry_l O hZF hp
      (check_name_l M (check_range_l M hZF) hb ht) ha ((hγ.2 t a).mpr ⟨ha, ht⟩) hpa

/-- 名称值精确等于泛型所接受的旧条件的规范像。 -/
theorem gname_value_l (hZF : M.Models ZF) {B R z b γ U}
    (O : Cond_order_d M B R z) (hU : Generic_d M B R z U) (hγ : Gname_d (M := M) B b γ)
    {Y : (extension_l M hZF B R z U).Domain} (hY : Qval_d M B R z U γ Y)
    (e : M.Domain → (extension_l M hZF B R z U).Domain)
    (he : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a))
    (x : (extension_l M hZF B R z U).Domain) : x ∈ Y ↔ ∃ p, U p ∧ e p = x := by
  rw [qval_mem_l O hZF hU hY]
  constructor
  · rintro ⟨t, p, htp, hp, ht⟩
    exact ⟨p, hp, qval_unique_l (he p t ((hγ.2 t p).mp htp).2) ht⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨t, ht⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b p
    exact ⟨t, p, (hγ.2 t p).mpr ⟨(hU.proper p hp).1, ht⟩, hp, he p t ht⟩

end YesMetaZFC.Model.Forcing.Internal
