import YesMetaZFC.Model.Forcing.Iteration.Stage.Basic
import YesMetaZFC.SetTheory.Ord.Recursion

/-! # 模型内编码的坐标阶段系统

条件集与序关系分别由模型中的序数序列编码。每两个按包含排列的阶段具有
实际限制投影与前缀提升；零系统和名称后继装配都返回这些完整证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

structure Row_system_d (I : kpair_convention_l.Interpretation M) (δ F H e : M.Domain) : Prop where
  conditions : M.IsSequenceOfLength I F δ
  relations : M.IsSequenceOfLength I H δ
  empty : ∀ x, ¬ M.mem x e
  stages : ∀ α B R, Entry_d M α B F → Entry_d M α R H → Row_stage_d M α B R e
  links : ∀ α β B R D V, Entry_d M α B F → Entry_d M α R H →
    Entry_d M β D F → Entry_d M β V H → M.MemberSubset α β → Row_link_d I α B R D V

def Row_system_supp_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (k : Bool) (ω F : M.Domain) : Prop :=
  ∀ α B, Entry_d M α B F → ∀ p, M.mem p B → Row_supp_d I k ω p

/-- 两张实际阶段图同步截取后仍是完整系统；允许截取到整个原定义域。 -/
theorem row_system_restrict_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {δ F G b γ F' G'}
    (h : Row_system_d (kpair_interpretation_l M hE hP) δ F G b) (hγ : M.IsOrdinal γ)
    (hγδ : M.MemberSubset γ δ) (hF : M.IsRestrictionOf (kpair_interpretation_l M hE hP) F' F γ)
    (hG : M.IsRestrictionOf (kpair_interpretation_l M hE hP) G' G γ) :
    Row_system_d (kpair_interpretation_l M hE hP) γ F' G' b := by
  refine ⟨⟨hγ, hF.isSetFunction h.conditions.2.1, hF.isDomainOf h.conditions.2.2 hγδ⟩,
    ⟨hγ, hG.isSetFunction h.relations.2.1, hG.isDomainOf h.relations.2.2 hγδ⟩, h.empty,
    fun α B R hB hR => h.stages α B R ((hF.2 α B).mp hB).2 ((hG.2 α R).mp hR).2, ?_⟩
  intro α β B R D V hB hR hD hV hαβ
  exact h.links α β B R D V ((hF.2 α B).mp hB).2 ((hG.2 α R).mp hR).2
    ((hF.2 β D).mp hD).2 ((hG.2 β V).mp hV).2 hαβ

/-- 空的内部阶段序列，是统一极限装配在零长度处的实际输入。 -/
theorem row_system_empty_l (M : SetTheory.Structure.{u}) (hKP : M.Models KP) : ∃ e,
    Row_system_d (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)) e e e e := by
  let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  have hs := Structure.IsSequenceOfLength.empty I he
  have noE i s (hh : Entry_d M i s e) : False := hh.elim fun v hv => he v hv.2
  exact ⟨e, hs, hs, he, fun α B _ hB _ => False.elim (noE α B hB),
    fun α _ B _ _ _ hB _ _ _ _ => False.elim (noE α B hB)⟩

/-- 把带全部早期投影的实际阶段写入序列末端，供名称后继和支撑极限共同使用。 -/
theorem row_system_extend_l (hKP : M.Models KP) {δ μ F H e D V}
    (h : Row_system_d (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)) δ F H e)
    (hμ : M.SuccessorOf μ δ) (hD : Row_stage_d M δ D V e)
    (hNext : ∀ α B R, Entry_d M α B F → Entry_d M α R H →
      Row_link_d (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)) α B R D V) :
    ∃ F' H', Row_system_d (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)) μ F' H' e ∧
      (∀ i p, Entry_d M i p F' ↔ Entry_d M i p F ∨ (i = δ ∧ p = D)) ∧
      (∀ i p, Entry_d M i p H' ↔ Entry_d M i p H ∨ (i = δ ∧ p = V)) ∧
      ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, Row_system_supp_d I k ω F →
        (∀ p, M.mem p D → Row_supp_d I k ω p) → Row_system_supp_d I k ω F' := by
  let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
  have hμo := KP.successor_isOrdinal hKP h.conditions.1 hμ
  obtain ⟨F', hFs, hF⟩ := Structure.IsSequenceOfLength.exists_append (value := D) hKP I h.conditions hμo hμ
  obtain ⟨H', hHs, hH⟩ := Structure.IsSequenceOfLength.exists_append (value := V) hKP I h.relations hμo hμ
  have idx i p (hip : Entry_d M i p F) : M.mem i δ := (h.conditions.2.2 i).mpr ⟨p, hip⟩
  have idxR i p (hip : Entry_d M i p H) : M.mem i δ := (h.relations.2.2 i).mpr ⟨p, hip⟩
  have noF p (hp : Entry_d M δ p F) : False := KP.mem_irrefl_d hKP δ (idx δ p hp)
  have noH p (hp : Entry_d M δ p H) : False := KP.mem_irrefl_d hKP δ (idxR δ p hp)
  have stage i p s (hip : Entry_d M i p F') (his : Entry_d M i s H') : Row_stage_d M i p s e := by
    rcases (hF i p).mp hip with hip | ⟨rfl, rfl⟩ <;> rcases (hH _ s).mp his with his | ⟨hi, hs⟩
    · exact h.stages i p s hip his
    · subst i
      exact False.elim (noF p hip)
    · exact False.elim (noH s his)
    · subst s
      exact hD
  have supp {𝒞 : OrderedPairConvention} (J : 𝒞.Interpretation M) k ω
      (hs : Row_system_supp_d J k ω F) (hd : ∀ p, M.mem p D → Row_supp_d J k ω p) :
      Row_system_supp_d J k ω F' := by
    intro i P hi p hp
    rcases (hF i P).mp hi with hi | ⟨_, he⟩
    · exact hs i P hi p hp
    · subst P
      exact hd p hp
  refine ⟨F', H', ⟨hFs, hHs, h.empty, stage, ?_⟩, hF, hH, supp⟩
  intro i j p s q t hip his hjq hjt hij
  classical
  by_cases hi : i = δ
  · subst i
    have hp := ((hF δ p).mp hip).resolve_left (noF p)
    have hs := ((hH δ s).mp his).resolve_left (noH s)
    rcases (hF j q).mp hjq with hjq | ⟨hj, hq⟩
    · exact False.elim (KP.mem_irrefl_d hKP j (hij j (idx j q hjq)))
    · subst j
      have ht := ((hH δ t).mp hjt).resolve_left (noH t)
      obtain ⟨_, rfl⟩ := hp
      obtain ⟨_, rfl⟩ := hs
      subst q
      obtain ⟨_, rfl⟩ := ht
      exact row_link_id_l hKP.1 (KP.exists_pair hKP) hD.order hD.rows
  · have hip := ((hF i p).mp hip).resolve_right (fun hh => hi hh.1)
    have his := ((hH i s).mp his).resolve_right (fun hh => hi hh.1)
    by_cases hj : j = δ
    · subst j
      have hq := (((hF δ q).mp hjq).resolve_left (noF q)).2
      have ht := (((hH δ t).mp hjt).resolve_left (noH t)).2
      subst q
      subst t
      exact hNext i p s hip his
    · exact h.links i j p s q t hip his
        (((hF j q).mp hjq).resolve_right (fun hh => hj hh.1))
        (((hH j t).mp hjt).resolve_right (fun hh => hj hh.1)) hij

end YesMetaZFC.Model.Forcing.Internal
