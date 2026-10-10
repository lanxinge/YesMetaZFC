import YesMetaZFC.Model.Forcing.Proper.Hereditary.NameBound
import YesMetaZFC.Model.Forcing.Internal.Functions.Rules

/-! # 按旧索引与条件选择小子名称

单射值及条件共同索引子名称；每个槽位只选择一个遗传小代表。候选不存在时
返回空名称，后续加权装配只使用有候选的槽位。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Hchild_d (M : SetTheory.Structure.{u}) (B R z b f t p i q s : M.Domain) : Prop :=
  Name_d M B s ∧ ∃ v a, Entry_d M v a t ∧ Below_d M B R z q p ∧ Entry_d M q a R ∧
    Nvalue_d M B R z b f q v i ∧ Eq_force_d M B R z q s v

def hchild_m {n} (B R z b f t p i q s : Term n) : Formula 1 n :=
  .conj (name_m B s) (.existsE (.existsE
    (.conj (entry_m (.bound 1) .newest t.weaken.weaken)
      (.conj (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken q.weaken.weaken p.weaken.weaken)
        (.conj (entry_m q.weaken.weaken .newest R.weaken.weaken)
          (.conj (nvalue_m B.weaken.weaken R.weaken.weaken z.weaken.weaken b.weaken.weaken
            f.weaken.weaken q.weaken.weaken (.bound 1) i.weaken.weaken)
            (eq_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken q.weaken.weaken
              s.weaken.weaken (.bound 1))))))))
derive_free_closed hchild_m

theorem hchild_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f t p i q s : Term n) :
    Formula.satisfies ρ (hchild_m B R z b f t p i q s) ↔
      Hchild_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (t.eval ρ)
        (p.eval ρ) (i.eval ρ) (q.eval ρ) (s.eval ρ) := by
  simp only [hchild_m, Hchild_d, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    name_sat_l M hE, entry_sat_l M hE, below_sat_l M hE, nvalue_sat_l hE, eq_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

/-- 选择图来自对象模型的选择公理，值域确实包含于 H，且每个值都是名称。 -/
theorem hchild_choice_l (hZFC : M.Models ZFC) {B R z b f t p H u D μ}
    (hu : M.mem u H) (huN : Name_d M B u)
    (hD : M.IsCartesianProduct (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) D μ B) :
    ∃ G A, M.IsSetFunctionFromTo (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) G D A ∧
      M.IsSetSurjectiveOnto (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) G D A ∧
      M.MemberSubset A H ∧ (∀ s, M.mem s A → Name_d M B s) ∧
      ∀ k s i q, Entry_d M k s G → KPair_d M k i q →
        (∃ v, M.mem v H ∧ Hchild_d M B R z b f t p i q v) → Hchild_d M B R z b f t p i q s := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 9 := ((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f).push t).push p).push H).push u
  let φ : BinarySchema 9 := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (.disj (hchild_m (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
        (.bound 6) (.bound 1) .newest (.bound 2))
        (.conj (.neg (.existsE (.conj (.mem .newest (.bound 6))
          (hchild_m (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
            (.bound 7) (.bound 2) (.bound 1) .newest))))
          (Formula.extensionalEq (.bound 2) (.bound 4)))))) }
  have hφ k s : φ.denote ρ k s ↔ ∃ i q, KPair_d M k i q ∧
      (Hchild_d M B R z b f t p i q s ∨
        ((¬ ∃ v, M.mem v H ∧ Hchild_d M B R z b f t p i q v) ∧ s = u)) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
      kpair_sat_l M hZFC.1, hchild_sat_l hZFC.1, Formula.satisfies_extensionalEq_iff_eq hZFC.1]
    rfl
  obtain ⟨G, hG, hg⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := H) (by
    intro k hk
    obtain ⟨i, _, q, _, hk⟩ := (hD k).mp hk
    by_cases h : ∃ s, M.mem s H ∧ Hchild_d M B R z b f t p i q s
    · obtain ⟨s, hs, h⟩ := h
      exact ⟨s, hs, (hφ k s).mpr ⟨i, q, hk, Or.inl h⟩⟩
    · exact ⟨u, hu, (hφ k u).mpr ⟨i, q, hk, Or.inr ⟨h, rfl⟩⟩⟩)
  obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hG.1 hG.2.1
  have hAS : M.MemberSubset A H := fun s hs => by
    obtain ⟨k, hk⟩ := (hA s).mp hs
    exact hG.output_mem_of_pairMember hk
  refine ⟨G, A, ⟨hG.1, hG.2.1,
    fun k hk => (hG.2.2 k hk).elim fun s hs => ⟨s, (hA s).mpr ⟨k, hs.2⟩, hs.2⟩⟩,
    ?_, hAS, ?_, ?_⟩
  · intro s hs
    obtain ⟨k, hk⟩ := (hA s).mp hs
    exact ⟨k, hG.input_mem_of_pairMember hk, hk⟩
  · intro s hs
    obtain ⟨k, hk⟩ := (hA s).mp hs
    obtain ⟨_, _, _, h⟩ := (hφ k s).mp (hg k s hk)
    exact h.elim And.left (fun h => h.2.symm ▸ huN)
  · intro k s i q hk hi hc
    obtain ⟨j, r, hr, h⟩ := (hφ k s).mp (hg k s hk)
    obtain ⟨hij, hqr⟩ := kpair_injective_l M hi hr
    subst j; subst r
    exact h.elim id (fun h => (h.1 hc).elim)

end YesMetaZFC.Model.Forcing.Internal
