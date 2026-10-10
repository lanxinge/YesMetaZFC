import YesMetaZFC.Model.Forcing.Iteration.Closed.Fusion
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Basic
import YesMetaZFC.SetTheory.Card.Cofinality.Countable
import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness

/-! # 任意内部极限的可数闭区间

原下降链的支撑并内部可数。有界时整条链已经落在一个较早阶段；共尾时截取
指定旧前缀以上的支撑，构造严格 ω 共尾列及相容下界前缀，再精确融合。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_cl_limit_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b β}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (h : Row_iteration_d I true ω b φ ρ δ F G)
    (hβ : M.IsLimitOrdinal β) (hPast : ∀ ξ, M.mem ξ β → Row_cl_stage_d I ω F G ξ) :
    Row_cl_stage_d I ω F G β := by
  intro α B R D V hαβ hB hR hD hV
  have hαδ := (h.1.conditions.2.2 α).mpr ⟨B, hB⟩
  have hβδ := (h.1.conditions.2.2 β).mpr ⟨D, hD⟩
  rcases h.1.conditions.1.wellOrder.linear.compare α hαδ β hβδ with he | hαβ' | hβα
  · have he := hZFC.1.eq_of_same_members α β he
    subst α
    have heB := h.1.conditions.2.1.2 β B D hB hD
    have heR := h.1.relations.2.1.2 β R V hR hV
    subst B R
    exact row_cl_id_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) (h.1.stages β D V hD hV)
  · intro f p hf hp hpf
    obtain ⟨J, hJ⟩ := ZF.exists_range_of_setFunction hZF I hf.1.1 hf.1.2.1
    have hFJ : M.IsSetFunctionFromTo I f ω J := ⟨hf.1.1, hf.1.2.1, fun i hi => by
      obtain ⟨r, _, hir⟩ := hf.1.2.2 i hi
      exact ⟨r, (hJ r).mpr ⟨i, hir⟩, hir⟩⟩
    have hJc : M.CardinalLessOrEqual I J ω := ZFC.surjection_bound_l I hZFC hFJ (fun r hr => by
      obtain ⟨i, hir⟩ := (hJ r).mp hr
      exact ⟨i, hf.1.input_mem_of_pairMember hir, hir⟩)
    obtain ⟨C, hC, hCc⟩ := row_countable_coords_l hZFC hω hJc (fun r hr => by
      obtain ⟨i, hir⟩ := (hJ r).mp hr
      exact h.2.1 β D hD r (hf.1.output_mem_of_pairMember hir))
    have hCβ : M.MemberSubset C β := by
      intro ξ hξ
      obtain ⟨r, hr, s, hξs⟩ := (hC ξ).mp hξ
      obtain ⟨i, hir⟩ := (hJ r).mp hr
      exact (h.1.stages β D V hD hV).rows r (hf.1.output_mem_of_pairMember hir) |>.domain ξ s hξs
    rcases Structure.bounded_or_cofinalSubset hZF hβ hCβ with hBound | hCof
    · obtain ⟨η, hηβ, hCη⟩ := hBound.exists_bound
      have upper : ∃ γ, M.mem γ β ∧ M.mem α γ ∧ M.mem η γ := by
        rcases hβ.1.wellOrder.linear.compare α hαβ' η hηβ with he | haη | hηa
        · obtain ⟨γ, hγ, hηγ⟩ := hβ.2.2 η hηβ
          exact ⟨γ, hγ, (hZFC.1.eq_of_same_members α η he).symm ▸ hηγ, hηγ⟩
        · obtain ⟨γ, hγ, hηγ⟩ := hβ.2.2 η hηβ
          exact ⟨γ, hγ, (hβ.1.mem hγ).transitive η hηγ α haη, hηγ⟩
        · obtain ⟨γ, hγ, hαγ⟩ := hβ.2.2 α hαβ'
          exact ⟨γ, hγ, hαγ, (hβ.1.mem hγ).transitive α hαγ η hηa⟩
      obtain ⟨γ, hγβ, hαγ, hηγ⟩ := upper
      have hCγ : M.MemberSubset C γ := fun ξ hξ => (hCη ξ hξ).elim
        (fun he => he.symm ▸ hηγ) (fun hξη => (hβ.1.mem hγβ).transitive η hηγ ξ hξη)
      have hγδ := h.1.conditions.1.transitive β hβδ γ hγβ
      obtain ⟨E, hE⟩ := (h.1.conditions.2.2 γ).mp hγδ
      obtain ⟨T, hT⟩ := (h.1.relations.2.2 γ).mp hγδ
      have k := h.1.links γ β E T D V hE hT hD hV (hβ.1.transitive.memberSubset hγβ)
      have earlier {i r} (hir : Entry_d M i r f) : M.mem r E := by
        have hrD := hf.1.output_mem_of_pairMember hir
        have hr := (h.1.stages β D V hD hV).rows r hrD
        have hrγ : Row_d M γ r := ⟨hr.graph, hr.functional,
          fun ξ s hξs => hCγ ξ ((hC ξ).mpr ⟨r, (hJ r).mpr ⟨i, hir⟩, s, hξs⟩)⟩
        obtain ⟨a, ha, har⟩ := k.restrict r hrD
        have he := har.eq hZFC.1 ⟨hrγ.graph, fun ξ s => ⟨fun hξs => ⟨hrγ.domain ξ s hξs, hξs⟩, And.right⟩⟩
        exact he ▸ ha
      have hfe : Chain_d I E T E ω f := by
        refine ⟨⟨hf.1.1, hf.1.2.1, fun i hi => ?_⟩,
          fun i r hir he => KP.mem_irrefl_d (ZF.modelsKP hZF) E (he ▸ earlier hir), ?_⟩
        · obtain ⟨r, _, hir⟩ := hf.1.2.2 i hi
          exact ⟨r, earlier hir, hir⟩
        · intro i j r s hij hir hjs
          exact (k.order s r (earlier hjs) (earlier hir)).mp (hf.2.2 i j r s hij hir hjs)
      obtain ⟨q, hq, hpq, hqf⟩ := hPast γ hγβ α B R E T ((hβ.1.mem hγβ).transitive.memberSubset hαγ)
        hB hR hE hT f p hfe hp hpf
      exact ⟨q, k.mem q hq, hpq, fun i r hir => (k.order q r hq (earlier hir)).mpr (hqf i r hir)⟩
    · -- 去掉旧前缀以下的支撑后仍然共尾，并保持原来的可数单射界。
      let η : Env M 1 := ⟨fun _ => α, fun _ => α⟩
      let ψ : UnarySchema 1 := { body := .mem (.bound 1) .newest }
      obtain ⟨C', hC'⟩ := ZF.separation_exists_d hZF ψ η C
      have mem x : M.mem x C' ↔ M.mem x C ∧ M.mem α x := by
        simpa only [ψ, Formula.satisfies_mem_iff] using! hC' x
      have hC'β : M.MemberSubset C' β := fun x hx => hCβ x ((mem x).mp hx).1
      have hc' : M.IsCofinalSubset C' β := by
        refine ⟨hβ, hC'β, fun x => ⟨fun hx => ?_, ?_⟩⟩
        · obtain ⟨a, ha, hαa⟩ := (hCof.2.2 α).mp hαβ'
          rcases hβ.1.wellOrder.linear.compare x hx α hαβ' with he | hxa | hαx
          · exact ⟨a, (mem a).mpr ⟨ha, hαa⟩, (hZFC.1.eq_of_same_members x α he).symm ▸ hαa⟩
          · exact ⟨a, (mem a).mpr ⟨ha, hαa⟩, (hβ.1.mem (hCβ a ha)).transitive α hαa x hxa⟩
          · obtain ⟨y, hy, hxy⟩ := (hCof.2.2 x).mp hx
            exact ⟨y, (mem y).mpr ⟨hy, (hβ.1.mem (hCβ y hy)).transitive x hxy α hαx⟩, hxy⟩
        · rintro ⟨y, hy, hxy⟩
          exact hβ.1.transitive y (hC'β y hy) x hxy
      obtain ⟨j, hj⟩ := ZF.exists_inclusionInjection hZF I (fun x hx => ((mem x).mp hx).1)
      obtain ⟨k, hk⟩ := hCc
      obtain ⟨A, hAC, hA⟩ := ZF.cc_strict_cofinal_l I hZF hω hc' (ZF.exists_compositionInjection hZF I hj hk)
      have ha i ξ (hiξ : Entry_d M i ξ A) : M.MemberSubset α ξ :=
        (hβ.1.mem (hAC.mono_target_l I hC'β |>.output_mem_of_pairMember hiξ)).transitive.memberSubset
          ((mem ξ).mp (hAC.output_mem_of_pairMember hiξ)).2
      obtain ⟨X, Q, q₀, hQ, hq₀, hpq₀, hv, hs⟩ := row_cl_thread_l hZFC hω h.1 hD hV hf hA hPast hB hR hp hpf ha
      obtain ⟨F', G', hF', hG', _, hl⟩ := row_iteration_limit_l hZF hω hRule h hβ hD hV
      obtain ⟨q, hq, hpre, hqf⟩ := row_cl_fuse_l hZFC hω h.1 hD hV hF' hG' h.2.1 hl hA hQ
        (fun _ _ hir => hf.1.output_mem_of_pairMember hir) hv hs
      obtain ⟨ξ₀, _, hiξ₀⟩ := hAC.2.2 b (hQ.input_mem_of_pairMember hq₀)
      exact ⟨q, hq, hpq₀.comp_l (hpre b ξ₀ q₀ hiξ₀ hq₀) (ha b ξ₀ hiξ₀), hqf⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) β (hαβ β hβα)).elim

end YesMetaZFC.Model.Forcing.Internal
